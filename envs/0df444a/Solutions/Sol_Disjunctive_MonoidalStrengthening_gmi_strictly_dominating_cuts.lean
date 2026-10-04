-- Prove2me | solution 1 for Disjunctive.MonoidalStrengthening.gmi_strictly_dominating_cuts
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:29:20.072866+00:00
-- url     : https://prove2.me/submissions/a2d9966a-b2ac-4cea-abc0-436f28d9fff6

import Mathlib
import Definitions.Def_Disjunctive_MonoidalStrengthening_Basic

open Disjunctive.MonoidalStrengthening

theorem solution : ¬ (∀ {n : ℕ} (a0 : ℝ) (a : Fin n → ℝ) (J1 : Finset (Fin n))
    (ha0 : 0 < a0) (ha0' : a0 < 1)
    (x : Fin n → ℝ) (hx_nonneg : 0 ≤ x) (hx_int : ∀ j ∈ J1, ∃ k : ℤ, x j = (k : ℝ))
    (hx_disj : a0 - ∑ j, a j * x j ≤ 0 ∨ 1 ≤ a0 - ∑ j, a j * x j),
    1 ≤ ∑ j, AlphaPlus a0 a J1 j * x j ∧ 1 ≤ ∑ j, AlphaMinus a0 a J1 j * x j) := by
  intro h
  have key := (h (n := 1) (1 / 2) (fun _ => 3 / 2) Finset.univ (by norm_num) (by norm_num)
    (fun _ => 1) (fun _ => zero_le_one) (fun _ _ => ⟨1, by simp⟩)
    (Or.inl (by simp; norm_num))).1
  simp [AlphaPlus] at key
  norm_num at key

#print axioms solution
