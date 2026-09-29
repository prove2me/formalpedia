-- Prove2me | solution 1 for Freiman.upper_choice_path
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T20:40:34.721407+00:00
-- url     : https://prove2.me/submissions/51d32bea-3b40-4236-8032-96f59db5e4f5

import Definitions.Def_Freiman_upperModel

open Freiman

private theorem normal_tree_length_positive
    (T : List Bool → upperInterval) (hT : upperNormalTree T) (w : List Bool) :
    0 < upperLength (T w) := by
  rcases hT w with ⟨hl, hr, hg, hpl, hpr, _, _⟩
  unfold upperLength at *
  linarith

private theorem derived_comm (C D : upperInterval) : upperDerived C D = upperDerived D C := by
  simp only [upperDerived, add_comm, min_comm]

theorem solution
    (step : ∀ C D L R : upperInterval, 0 < upperLength C → upperLength C ≤ upperLength D →
      upperNormalSplit D L R → upperDerived C D ⊆ upperDerived C L ∪ upperDerived C R)
    (T S : List Bool → upperInterval) (hT : upperNormalTree T) (hS : upperNormalTree S)
    (z : ℝ) (hz : z ∈ upperDerived (T []) (S [])) :
    ∃ u v : ℕ → List Bool, upperPath T S u v z := by
  classical
  let State := {a : List Bool × List Bool // z ∈ upperDerived (T a.1) (S a.2)}
  let Rel : State → State → Prop := fun a b =>
    (upperLength (S a.1.2) ≤ upperLength (T a.1.1) ∧
      ∃ c, b.1.1 = a.1.1 ++ [c] ∧ b.1.2 = a.1.2) ∨
    (upperLength (T a.1.1) ≤ upperLength (S a.1.2) ∧
      ∃ c, b.1.2 = a.1.2 ++ [c] ∧ b.1.1 = a.1.1)
  have hnext : ∀ a : State, ∃ b : State, Rel a b := by
    intro a
    by_cases hle : upperLength (S a.1.2) ≤ upperLength (T a.1.1)
    · have hin : z ∈ upperDerived (S a.1.2) (T a.1.1) := by
        rw [derived_comm]
        exact a.2
      have hc := step (S a.1.2) (T a.1.1) (T (a.1.1 ++ [false])) (T (a.1.1 ++ [true]))
        (normal_tree_length_positive S hS _) hle (hT _) hin
      rcases hc with hc | hc
      · have hd : z ∈ upperDerived (T (a.1.1 ++ [false])) (S a.1.2) := by
          rw [derived_comm]
          exact hc
        exact ⟨⟨(a.1.1 ++ [false], a.1.2), hd⟩, Or.inl ⟨hle, false, rfl, rfl⟩⟩
      · have hd : z ∈ upperDerived (T (a.1.1 ++ [true])) (S a.1.2) := by
          rw [derived_comm]
          exact hc
        exact ⟨⟨(a.1.1 ++ [true], a.1.2), hd⟩, Or.inl ⟨hle, true, rfl, rfl⟩⟩
    · have hle' := le_of_not_ge hle
      have hc := step (T a.1.1) (S a.1.2) (S (a.1.2 ++ [false])) (S (a.1.2 ++ [true]))
        (normal_tree_length_positive T hT _) hle' (hS _) a.2
      rcases hc with hc | hc
      · exact ⟨⟨(a.1.1, a.1.2 ++ [false]), hc⟩, Or.inr ⟨hle', false, rfl, rfl⟩⟩
      · exact ⟨⟨(a.1.1, a.1.2 ++ [true]), hc⟩, Or.inr ⟨hle', true, rfl, rfl⟩⟩
  let f : State → State := fun a => (hnext a).choose
  have hf : ∀ a : State, Rel a (f a) := fun a => (hnext a).choose_spec
  let path : ℕ → State := Nat.rec ⟨([], []), hz⟩ (fun _ a => f a)
  refine ⟨fun n => (path n).1.1, fun n => (path n).1.2, rfl, rfl, ?_, ?_⟩
  · intro n
    exact (path n).2
  · intro n
    exact hf (path n)
