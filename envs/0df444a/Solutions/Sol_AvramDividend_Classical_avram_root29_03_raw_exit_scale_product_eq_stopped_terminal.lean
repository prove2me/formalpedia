-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_raw_exit_scale_product_eq_stopped_terminal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:04:54.281048+00:00
-- url     : https://prove2.me/submissions/ff0ef242-89ae-4a18-bbf6-9f548517bf32

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_standing_stopped_min_terminal_factorisation

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The exact raw inline two-sided upper-exit lintegral times the upper
scale value equals the original stopped-minimum discounted terminal scale
reward under Standing, with no killed-harmonicity hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) * ENNReal.ofReal (W a) =
    (∫⁻ ω, if min (twoSidedExitUpTime X (a - x) ω)
            (twoSidedExitDownTime X (-x) ω) < ⊤ then
      ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (min (twoSidedExitUpTime X (a - x) ω)
              (twoSidedExitDownTime X (-x) ω))))) *
        ENNReal.ofReal
          (W (x + X.X (min (twoSidedExitUpTime X (a - x) ω)
            (twoSidedExitDownTime X (-x) ω)).toNNReal ω))
      else 0 ∂P) := by
  change twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
    (∫⁻ ω, if min (twoSidedExitUpTime X (a - x) ω)
            (twoSidedExitDownTime X (-x) ω) < ⊤ then
      ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (min (twoSidedExitUpTime X (a - x) ω)
              (twoSidedExitDownTime X (-x) ω))))) *
        ENNReal.ofReal
          (W (x + X.X (min (twoSidedExitUpTime X (a - x) ω)
            (twoSidedExitDownTime X (-x) ω)).toNNReal ω))
      else 0 ∂P)
  exact (avram_root29_03_standing_stopped_min_terminal_factorisation
    X hX q hq W hW a x ha hx0 hxa).symm
