-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_scale_deriv_not_continuousWithinAt_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:13:06.187327+00:00
-- url     : https://prove2.me/submissions/edcbef87-d6e4-4cfe-8f30-beabddb21fa0

import Mathlib.Topology.NhdsWithin
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_derivRightLimit_at_zero_eq_two_over_sigma
import Theorems.Thm_AvramDividend_Classical_gaussian_scale_ordinary_deriv_ne_positive_right_slope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

/-- The two-sided origin derivative cannot match its positive Gaussian slope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    ¬ ContinuousWithinAt (deriv W) (Ici (0 : ℝ)) 0 := by
  intro hcont
  have hzero : W 0 = 0 :=
    scaleFunction_zero_origin_gaussian_without_standing X q hq W hW hσ
  have hC1 := scaleFunction_contDiff_one_gaussian_without_standing
    X q hq W hW hσ
  have hderiv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt W (deriv W x) x := by
    intro x hx
    exact ((hC1.contDiffAt (isOpen_Ioi.mem_nhds hx)).differentiableAt
      (by norm_num)).hasDerivAt
  have hright := scaleFunction_derivRightLimit_at_zero_eq_two_over_sigma
    X q hq W hW hσ hzero hderiv
  have hsub : Ioi (0 : ℝ) ⊆ Ici (0 : ℝ) := by
    intro x hx
    exact le_of_lt (mem_Ioi.mp hx)
  have hcontRight : Tendsto (deriv W) (𝓝[>] (0 : ℝ))
      (𝓝 (deriv W 0)) := hcont.mono hsub
  have heq : deriv W 0 = 2 / X.σ ^ 2 :=
    tendsto_nhds_unique hcontRight hright
  exact (gaussian_scale_ordinary_deriv_ne_positive_right_slope
    X q hq W hW hσ) heq