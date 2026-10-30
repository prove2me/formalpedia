-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_standing_killed_min_to_raw_exit_ratio
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:04:00.744531+00:00
-- url     : https://prove2.me/submissions/75d6368c-333d-4aa1-a33e-9fb2675e9d71

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_standing_stopped_min_harmonicity_to_exit_ratio

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Given explicit genuine killed stopped-minimum harmonicity, the
raw source inline-infimum strict upper-before-ruin discounted
lintegral equals the corrected q-scale ratio. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (hKilled :
    (∫⁻ ω, if min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω) < ⊤ then
      ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω))))) *
        ENNReal.ofReal
          (W (x + X.X (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)).toNNReal ω)) else 0 ∂P) =
      ENNReal.ofReal (W x)) :
    (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W x / W a) := by
  have hRatio :=
    avram_root29_03_standing_stopped_min_harmonicity_to_exit_ratio
      X hX q hq W hW a x ha hx0 hxa hKilled
  change twoSidedExitExpectation X q a x =
    ENNReal.ofReal (W x / W a)
  exact hRatio
