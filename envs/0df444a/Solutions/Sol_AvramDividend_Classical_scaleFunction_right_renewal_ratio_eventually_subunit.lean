-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_right_renewal_ratio_eventually_subunit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T17:51:13.038644+00:00
-- url     : https://prove2.me/submissions/df7265ae-77d1-40ed-8541-efcb06c52824

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.OrderClosed
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_monotone_nonzero_derivative_eventually_right_increment
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a : ℝ) (ha : 0 < a)
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < ε ∧ 0 < W (a + ε) ∧
        0 ≤ W a / W (a + ε) ∧ W a / W (a + ε) < 1 := by
  have hm : Monotone W := scaleFunction_monotone X q W hW
  have hWa : 0 < W a :=
    scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  have hi : ∀ᶠ ε in 𝓝[>] (0 : ℝ), W a < W (a + ε) :=
    monotone_nonzero_derivative_eventually_right_increment W a hm hD hd
  have he : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := by
    change Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ)
    exact self_mem_nhdsWithin
  filter_upwards [hi, he] with ε hinc hpos
  have hWr : 0 < W (a + ε) := lt_trans hWa hinc
  refine ⟨hpos, hWr, ?_, ?_⟩
  · exact div_nonneg (le_of_lt hWa) (le_of_lt hWr)
  · exact (div_lt_one hWr).mpr hinc
