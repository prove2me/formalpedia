-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_lower_first_capped_terminal_scale_zero_ae_no_standing_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T08:14:53.281009+00:00
-- url     : https://prove2.me/submissions/efcb41cb-1381-4a20-9650-f4bbe5174525

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_strict_lower_exit_undershoot_ae_no_standing_public
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P,
      twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a-x) ω →
      (twoSidedExitDownTime X (-x) ω).toNNReal ≤ T →
      Real.exp (-(q * ((min (min (twoSidedExitUpTime X (a-x) ω) (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) * W (x + X.X (min (min (twoSidedExitUpTime X (a-x) ω) (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω) = 0 := by
  have hUndershoot := p2m81_bv_strict_lower_exit_undershoot_ae_no_standing_public X q φ hq hφ hroot W hW hBV a x ha hx0 hxa
  filter_upwards [hUndershoot] with ω hω
  intro hDown hCap
  have hmin : min (twoSidedExitUpTime X (a-x) ω) (twoSidedExitDownTime X (-x) ω) = twoSidedExitDownTime X (-x) ω := min_eq_right hDown.le
  have hneg := hω hDown
  have hzero : W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω) = 0 := hW.1 _ hneg
  simp only [hmin, min_eq_left hCap, hzero, mul_zero]
