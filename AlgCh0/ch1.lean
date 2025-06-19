import Mathlib.Data.Nat.Basic

namespace MySet
def Set (α : Type u) := α → Prop
def greater_than_5 : Set Nat := fun n => n > 5
local notation a" ∈ "S => S a
def subset (A B : Set α) : Prop := ∀ a, A a → B a
local notation A" ⊆ "B => subset A B
def union (A B : Set α) : Set α := fun x : α => A x ∨ B x
local notation A" ∪ "B => union A B
def inter (A B : Set α ) : Set α := fun x : α => A x ∧ B x
local notation A" ∩ "B => inter A B
def difference (A B : Set α) : Set α := fun x : α => A x ∧ ¬B x
local notation A" \\ "B => difference A B
def greater_than_6 : Set Nat := fun n => n > 6
def gt55 : Prop := 5 ∈ greater_than_5
example : gt55 → False := by
  intro h
  dsimp [gt55] at h
  rw [greater_than_5] at h
  apply Nat.not_lt.2 (Nat.le_refl 5) h
def diff56 : Set Nat := greater_than_5 \ greater_than_6
example : diff56 6 := by
  rw [diff56]
  rw [difference]
  constructor
  rw [greater_than_5]
  simp
  rw [greater_than_6]
  simp

def powerset (S : Set α) : Set (Set α) := fun s : Set α => s ⊆ S
example : powerset greater_than_5 greater_than_6 := by
  unfold powerset greater_than_5 greater_than_6
  rw [subset]
  intro a h
  have h1 : 5 < 6 := by decide
  exact Nat.lt_trans h1 h

inductive Prod (α : Type u) (β : Type v) where
| mk : α → β → Prod α β
local notation a" ⨯ "b => Prod a b
local notation "("a", "b")" => Prod.mk a b
def Prod.fst (p : α ⨯ β) : α :=
  match p with
  | (a, _) => a
def Prod.snd (p : α ⨯ β) : β :=
  match p with
  | (_, b) => b
local notation p".1" => Prod.fst p
local notation p".2" => Prod.snd p
def CartesianProduct (A : Set α) (B : Set β) : Set (α ⨯ β) :=
  fun p => A (p.1) ∧ B (p.2)

#eval (1, 1).1

example : (7, 7) ∈ CartesianProduct greater_than_5 greater_than_6 := by
  unfold CartesianProduct
  constructor
  rw [greater_than_5]
  simp
  rw [greater_than_6]
  simp

def finite (S : Set α) : Prop :=
  ∃ (n : ℕ) (f : {x : α // x ∈ S} → ℕ), Function.Injective f ∧ ∀ x, f x < n

def emptyset (α : Type) : Set α := fun _ => False

end MySet
