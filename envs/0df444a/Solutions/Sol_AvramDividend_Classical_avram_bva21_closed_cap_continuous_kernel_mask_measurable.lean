-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva21_closed_cap_continuous_kernel_mask_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:10:13.303203+00:00
-- url     : https://prove2.me/submissions/2cb5a80d-b0bf-4b05-aef0-9b7bc7eef733

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Continuous negative-mark kernels on the actual closed cap admit measurable zero extension. -/
theorem solution
    (C : ℝ≥0∞) (ψ : ℝ → ℝ)
    (hcont : ContinuousOn ψ
      {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C})
    (U : ℝ≥0 → ℝ) (hU : Measurable U) :
    Measurable (fun t : ℝ≥0 =>
      if 0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C then ψ (U t) else 0) := by
  classical
  let A : Set ℝ := {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C}
  have hA : MeasurableSet A := by
    dsimp [A]
    measurability
  have hPiece : Measurable (A.piecewise ψ (fun _ => (0 : ℝ))) :=
    hcont.measurable_piecewise continuousOn_const hA
  have hEq :
      (fun t : ℝ≥0 =>
        if 0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C then ψ (U t) else 0) =
      (fun t : ℝ≥0 => A.piecewise ψ (fun _ => (0 : ℝ)) (U t)) := by
    funext t
    simp [A, Set.piecewise]
  rw [hEq]
  exact hPiece.comp hU
