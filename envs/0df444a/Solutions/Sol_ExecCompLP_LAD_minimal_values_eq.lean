-- Prove2me | solution 1 for ExecCompLP.LAD.minimal_values_eq
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-17T16:52:20.167295+00:00
-- url     : https://prove2.me/submissions/a0d2f403-da75-4150-92f6-94db7af29b7a

import Theorems.Thm_ExecCompLP_LAD_lift_feasible
import Theorems.Thm_ExecCompLP_LAD_project_feasible

open ExecCompLP.LAD

theorem solution {n L : ℕ} [NeZero L]
    (x : Fin n → Fin L → ℝ) (sM sm : ℝ) (K : Finset (Fin L))
    (s : Fin L → ℝ) :
    ∀ t : ℝ,
      (∃ a : Fin n → ℝ, Feasible x sM sm a ∧ obj x K s a ≤ t) ↔
      (∃ (a : Fin n → ℝ) (u v : Fin L → ℝ),
        LPFeasible x sM sm K s a u v ∧ lpObj K u v ≤ t) := by
  intro t
  constructor
  · rintro ⟨a, ha, ht⟩
    obtain ⟨hfeas, heq⟩ := ExecCompLP.LAD.lift_feasible x sM sm K s a ha
    exact ⟨a, _, _, hfeas, heq.le.trans ht⟩
  · rintro ⟨a, u, v, hf, ht⟩
    obtain ⟨ha, hle⟩ := ExecCompLP.LAD.project_feasible x sM sm K s a u v hf
    exact ⟨a, ha, hle.trans ht⟩

