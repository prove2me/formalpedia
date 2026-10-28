-- Prove2me | solution 2 for AvramDividend.Classical.barrierSupValue_stopped_renewal_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:31:56.118024+00:00
-- url     : https://prove2.me/submissions/bc04a67d-fe21-46b6-a64b-5d6ae90a7109
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_one_step_scale_regeneration_upper
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_stopped_renewal_upper_of_eventual_expected_step
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_monotone_nonzero_derivative_eventually_right_increment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

/-! The original stopped upper bound needs only the true q-scale record step. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a : ℝ) (ha : 0 < a)
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      barrierSupValue X a q ≤
        ENNReal.ofReal (ε * W (a + ε) / (W (a + ε) - W a)) := by
  have hWa : 0 < W a :=
    scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  have hinc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), W a < W (a + ε) :=
    monotone_nonzero_derivative_eventually_right_increment W a
      (scaleFunction_monotone X q W hW) hD hd
  have heps : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hε
  apply barrierSupValue_stopped_renewal_upper_of_eventual_expected_step
    X hX q hq W hW a ha hD hd
  filter_upwards [hinc, heps] with ε hincε hε
  intro n
  exact killed_firstRecord_one_step_scale_regeneration_upper
    X hX q hq W hW a ε ha hε
      (lt_trans hWa hincε) (le_of_lt hWa) hincε n
