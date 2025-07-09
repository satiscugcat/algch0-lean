import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.RelClasses
import Mathlib.Data.Setoid.Partition
import Init.Core
import Init.Prelude
import Mathlib.Data.Quot
import Mathlib.Tactic

open Set

namespace Aluffi

-- Example sets
def greater_than_5 : Set ℕ := {n | n > 5}
def greater_than_6 : Set ℕ := {n | n > 6}

-- Membership and difference example
example : 5 ∈ greater_than_5 → False := by
  intro h
  simp [greater_than_5] at h

-- Difference of sets
def diff56 := greater_than_5 \ greater_than_6

example : 6 ∈ diff56 := by
  simp [diff56, mem_diff, greater_than_5, greater_than_6]

#check Nat.lt_of_lt_of_le

-- Power set
example : greater_than_6 ∈ powerset greater_than_5 := by
  simp only [powerset, subset_def, greater_than_6, greater_than_5]
  intro x hx
  simp at hx
  simp
  exact Nat.lt_of_lt_of_le (by decide) hx

-- Cartesian product using Set.prod
example : (7, 7) ∈ greater_than_5 ×ˢ greater_than_6 := by
  simp [mem_prod, greater_than_5, greater_than_6]

#print Set.Finite

-- Finiteness
example : {n | n < 5} ⊆ univ ∧ (Set.Finite {n | n < 5}) := by
  constructor
  · exact subset_univ _
  · apply Set.toFinite

-- Empty set
example : ∅ ⊆ greater_than_5 := empty_subset greater_than_5

open Finset

variable {α : Type*} [DecidableEq α]

example (A B : Finset α) (h : A ⊆ B) : A.card ≤ B.card :=
  Finset.card_le_card h

example (S₁ S₂ S₃ : Set β) : S₁ ∪ (S₂ ∪ S₃) = (S₁ ∪ S₂) ∪ S₃ := by
  symm
  exact Set.union_assoc S₁ S₂ S₃

example (S₁ S₂ S₃ : Set β) : S₁ ∪ (S₂ ∪ S₃) = (S₁ ∪ S₂) ∪ S₃ := by
  apply Set.Subset.antisymm
  . intro x hx
    rcases hx with h1 | h23
    . left
      left
      assumption
    . rcases h23 with h2 | h3
      . left
        right
        assumption
      . right
        assumption
  . intro x hx
    rcases hx with h12 | h3
    . rcases h12 with h1 | h2
      . left
        assumption
      . right
        left
        assumption
    right
    right
    assumption

variable {A : Type}

-- covers on the whole type and not a set

def Reflexive (R : A → A → Prop) : Prop :=
∀ x, R x x

def Symmetric (R : A → A → Prop) : Prop :=
∀ x y, R x y → R y x

def Transitive (R : A → A → Prop) : Prop :=
∀ x y z, R x y → R y z → R x z

def Equivalence (R : A → A → Prop) : Prop :=
Reflexive R ∧ Symmetric R ∧ Transitive R

structure Partition (S : Set α) where
  parts : Set (Set α)
  nonempty : ∀ s ∈ parts, s.Nonempty
  disjoint : ∀ s ∈ parts, ∀ t ∈ parts, s ≠ t → Disjoint s t
  covers : ⋃₀ parts = S

-- for sets

def Reflexive_on_set (S : Set β) (R : β → β → Prop) : Prop :=
∀ x ∈ S, R x x

def eq : Nat → Nat → Prop := fun n => fun m => n = m

example : Reflexive_on_set greater_than_5 eq := by
  intro x hx
  rw [eq]

def Symmetric_on_set (S : Set β) (R : β → β → Prop) : Prop :=
∀ x ∈ S, ∀ y ∈ S, R x y → R y x

def even_sum : Nat → Nat → Prop := fun n => fun m => (n + m) % 2 = 0

example : Symmetric_on_set greater_than_5 even_sum := by
  intro x hx y hy h
  rw [even_sum] at h
  rw [add_comm] at h
  rw [even_sum]
  assumption

def Transitive_on_set (S : Set β) (R : β → β → Prop) : Prop :=
∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, R x y → R y z → R x z

def less_than : Nat → Nat → Prop := fun n => fun m => n < m

example : Transitive_on_set greater_than_5 less_than := by
  intro x hx y hy z hz hxy hyz
  rw [less_than] at hxy
  rw [less_than] at hyz
  rw [less_than]
  exact Nat.lt_trans hxy hyz

def Equivalence_on_set (S : Set β) (R : β → β → Prop) :=
Reflexive_on_set S R ∧ Symmetric_on_set S R ∧ Transitive_on_set S R

def S₁ : Set Nat := {1, 2, 3, 4}
def S₂ : Set Nat := {1, 2}
def S₃ : Set Nat := {3, 4}
def P : Set (Set Nat) := {S₂, S₃}

example : Partition S₁ where
  parts := P
  nonempty := by
    intro X hX
    simp only [P, mem_insert_iff, mem_singleton_iff] at hX
    rcases hX with (rfl | rfl)
    all_goals simp [Set.Nonempty]
    . simp [S₂]
    . simp [S₃]
  disjoint := by
    intro s hs t ht h
    simp only [P, mem_insert_iff, mem_singleton_iff] at hs ht
    rcases hs with (rfl | rfl)
    . rcases ht with (rfl | rfl)
      . contradiction
      . unfold S₂ S₃
        simp [Disjoint]
        intro x h1 h2
        apply Set.Subset.antisymm
        . intro y h3
          have h4 : y ∈ {1, 2} := h1 h3
          have h5 : y ∈ {3, 4} := h2 h3
          simp at h4
          simp at h5
          rcases h4 with (rfl | rfl)
          . simp at h5
          . simp at h5
        . exact Set.empty_subset x
    . rcases ht with (rfl | rfl)
      . unfold S₂ S₃
        simp [Disjoint]
        intro x h1 h2
        apply Set.Subset.antisymm
        . intro y h3
          have h4 : y ∈ {3, 4} := h1 h3
          have h5 : y ∈ {1, 2} := h2 h3
          simp at h4
          simp at h5
          rcases h4 with (rfl | rfl)
          . simp at h5
          . simp at h5
        . exact Set.empty_subset x
      . contradiction
  covers := by
    rw [P]
    simp [sUnion]
    apply Set.Subset.antisymm
    intro x hx
    unfold S₂ S₃ at hx
    unfold S₁
    simp at hx
    simp
    rcases hx with h3 | h412
    . right
      right
      left
      assumption
    . rcases h412 with h4 | h12
      . right
        right
        right
        assumption
      . rcases h12 with h1 | h2
        . left
          assumption
        . right
          left
          assumption
    intro x hx
    simp [S₂, S₃]
    simp [S₁] at hx
    rcases hx with h1 | h234
    . right
      right
      left
      assumption
    . rcases h234 with h2 | h34
      . right
        right
        right
        assumption
      . rcases h34 with h3 | h4
        . left
          assumption
        . right
          left
          assumption

-- Quotient
#print Setoid
#check Setoid
#check _root_.Equivalence
#check Even.add
#check add_left_cancel
#check Even.sub
#print _root_.Equivalence
def re : Nat → Nat → Prop := fun a => fun b => Even (a + b)
def equivalence_re : _root_.Equivalence re := by
  constructor
  . simp [re]
  . simp [re]
    intro x y h1
    rw [add_comm]
    assumption
  . simp [re]
    intro x y z h1 h2
    have h3 : Even ((x + y) + (y + z)) := Even.add h1 h2
    rcases h1 with ⟨w1, h1⟩
    rcases h2 with ⟨w2, h2⟩
    rw [add_assoc] at h3
    rw [← add_assoc y y z] at h3
    rw [add_comm (y + y) z] at h3
    rw [← add_assoc x z] at h3
    have h4 : Even (y + y) := by use y
    rw [add_comm] at h3
    rw [Nat.even_add] at h3
    exact h3.mp h4

def sample_setoid : Setoid Nat := Setoid.mk re equivalence_re
#check Quotient
#print Quotient
#check Quot
#check Quotient.mk
#print Quotient.mk
def sample_quotient := Quotient sample_setoid
#check sample_quotient
#check Setoid.empty_notMem_classes
#check sample_setoid.classes
#check Setoid.classes_eqv_classes
#check Setoid.isPartition_classes
#check Setoid.IsPartition

--Chapter 1 Ex 1.2

def quotient (r : Setoid α) : Set (Set α) := r.classes

def quotient_partition (r : Setoid α) : Setoid.IsPartition (quotient r) :=
  Setoid.isPartition_classes r

--Chapter 1 Ex 1.6
def rel_a_b (a b : ℝ) : Prop := ∃ (z : ℤ), (b - a) = ↑z
def equivalence_rel_a_b : _root_.Equivalence rel_a_b := by
  constructor
  . intro x
    simp [rel_a_b]
    use 0
    simp
  . intro x y h
    simp [rel_a_b] at h
    simp [rel_a_b]
    rcases h with ⟨w, h⟩
    use -w
    have h1 : x - y = -(y - x) := by
      ring
    rw [h1]
    rw [h]
    simp
  . intro x y z h1 h2
    simp [rel_a_b]
    simp [rel_a_b] at h1
    simp [rel_a_b] at h2
    rcases h1 with ⟨w1, ha⟩
    rcases h2 with ⟨w2, hb⟩
    use (w2 + w1)
    have hc : (z - y) + (y - x) = w1 + w2 := by
      rw [hb]
      rw [ha]
      rw [add_comm]
    rw [sub_eq_neg_add] at hc
    rw [sub_eq_neg_add] at hc
    rw [add_comm (-y) z] at hc
    rw [add_comm (-x) y] at hc
    rw [← add_assoc] at hc
    rw [add_assoc z (-y) y] at hc
    simp at hc
    rw [sub_eq_neg_add]
    rw [add_comm]
    rw [hc]
    rw [add_comm]
    simp

end Aluffi
