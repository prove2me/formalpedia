-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_BV_candidate_one_sided_value_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:10:36.156448+00:00
-- url     : https://prove2.me/submissions/5036cdf8-11f7-4432-99d7-a9007f7481a4

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical
noncomputable section

/-- The original BV candidate is bounded on every one-sided compact reserve band, including ruin overshoots. -/
theorem solution (w : ℝ → ℝ)
  (hwCont : ContinuousOn w (Ici 0))
  (hwNeg : ∀ v : ℝ, v < 0 → w v = 0)
  (b : ℝ) (hb : 0 ≤ b) :
  ∃ R : ℝ, 0 ≤ R ∧ ∀ v : ℝ, v ≤ b → |w v| ≤ R := by
  have hContIcc : ContinuousOn w (Icc 0 b) :=
    hwCont.mono (by intro v hv; exact hv.1)
  obtain ⟨R, hR⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) b)).exists_bound_of_continuousOn hContIcc
  refine ⟨max R 0, le_max_right _ _, ?_⟩
  intro v hv
  by_cases hv0 : v < 0
  · rw [hwNeg v hv0]
    simp [le_max_right]
  · have hvI : v ∈ Icc (0 : ℝ) b := ⟨le_of_not_gt hv0, hv⟩
    calc
      |w v| = ‖w v‖ := (Real.norm_eq_abs _).symm
      _ ≤ R := hR v hvI
      _ ≤ max R 0 := le_max_left _ _
