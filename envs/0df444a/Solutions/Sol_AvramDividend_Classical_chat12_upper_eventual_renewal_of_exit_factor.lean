-- Prove2me | solution 1 for AvramDividend.Classical.chat12_upper_eventual_renewal_of_exit_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:06:14.738239+00:00
-- url     : https://prove2.me/submissions/762619cb-030c-452c-bb9b-f74951de12f7

import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_stopped_renewal_upper_of_eventual_expected_step
import Theorems.Thm_AvramDividend_Classical_chat12_killed_firstRecord_upper_step_of_trueExit
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Exponential

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
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0)
    (hExit : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W a / W (a + ε))) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      barrierSupValue X a q ≤
        ENNReal.ofReal (ε * W (a + ε) / (W (a + ε) - W a)) := by
  have heps : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hε
  apply barrierSupValue_stopped_renewal_upper_of_eventual_expected_step
    X hX q hq W hW a ha hD hd
  filter_upwards [heps, hExit] with ε hε hExitε
  intro n
  exact chat12_killed_firstRecord_upper_step_of_trueExit
    X hX q hq a ε ha hε (W a / W (a + ε)) hExitε n
