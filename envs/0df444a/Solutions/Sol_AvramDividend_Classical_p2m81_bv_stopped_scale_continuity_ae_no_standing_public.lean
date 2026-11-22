-- Prove2me | solution 1 for AvramDividend.Classical.p2m81_bv_stopped_scale_continuity_ae_no_standing_public
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T05:42:04.627653+00:00
-- url     : https://prove2.me/submissions/da2c45a4-8ab9-4965-a0af-cfaf62139396
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_p2m81_bv_stopped_min_away_zero_ae_no_standing_public
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuousAt_away_zero

open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Standing-free BV stopped q-scale is continuous at its realised finite two-sided exit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    ∀ᵐ ω ∂P,
      min (twoSidedExitUpTime X (a - x) ω)
        (twoSidedExitDownTime X (-x) ω) < ⊤ →
      ContinuousAt W (x + X.X (min (twoSidedExitUpTime X (a - x) ω)
        (twoSidedExitDownTime X (-x) ω)).toNNReal ω) := by
  have hnz := p2m81_bv_stopped_min_away_zero_ae_no_standing_public
    X q φ hq hφ hroot W hW hBV a x ha hx0 hxa
  filter_upwards [hnz] with ω hω
  intro hfin
  exact scaleFunction_continuousAt_away_zero X q W hW
    (x + X.X (min (twoSidedExitUpTime X (a - x) ω)
      (twoSidedExitDownTime X (-x) ω)).toNNReal ω) (hω hfin)
