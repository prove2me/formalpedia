-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_run1750_original_rightcont_full_cutoff_predictable_cell_orthogonal_past
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:29:48.762041+00:00
-- url     : https://prove2.me/submissions/1c6ebc83-255b-4c8c-904a-3eee10919997

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_conditional_martingale_step
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_raw_conditional_cross_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact original full-cutoff compensated physical jump cell is orthogonal to the past. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0) (cut : ℕ)
    (F : Ω → ℝ)
    (hF : StronglyMeasurable[𝓕.rightCont s] F)
    (hFL2 : MemLp F 2 P)
    (H : Ω → ℝ)
    (hH : StronglyMeasurable[𝓕.rightCont s] H)
    (L : ℝ) (hBound : ∀ ω, |H ω| ≤ L) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    (∫ ω, F ω * (H ω * ((N ω).toReal - r)) ∂P) = 0 := by
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
  let r : ℝ :=
    ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
  change (∫ ω, F ω * (H ω * ((N ω).toReal - r)) ∂P) = 0
  have hCell :=
    avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_conditional_martingale_step
      X s T cut H hH L hBound
  have hCellL2 : MemLp (fun ω => H ω * ((N ω).toReal - r)) 2 P := by
    simpa only [N, r] using hCell.1
  have hCellZero :
      P[(fun ω => H ω * ((N ω).toReal - r)) |
        𝓕.rightCont s] =ᵐ[P] (fun _ : Ω => 0) := by
    simpa only [N, r] using hCell.2.1
  obtain ⟨Y, hYX, hc, hσ, hνEq⟩ :=
    avram_wave5_04_source_rightCont_levy_lift X
  exact avram_p4_g_isometry_original_raw_conditional_cross_zero
    Y s F (fun ω => H ω * ((N ω).toReal - r))
    hF hFL2 hCellL2 hCellZero
