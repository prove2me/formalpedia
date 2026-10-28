-- Prove2me | solution 3 for AvramDividend.Classical.barrierSupValue_stopped_renewal_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:21:25.706091+00:00
-- url     : https://prove2.me/submissions/06176534-9fd4-4d08-8eae-21ccce90f54a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_integral_identity
import Theorems.Thm_AvramDividend_Classical_chat12_upper_eventual_renewal_of_exit_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Upper reflected reward bound from the raw two-sided-exit integral. -/
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
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε := by
    change Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ)
    exact self_mem_nhdsWithin
  have hExit : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W a / W (a + ε)) := by
    filter_upwards [hpos] with ε hε
    have hlevel : 0 < a + ε := by linarith
    have hxa : a ≤ a + ε := by linarith
    have hcore :=
      two_sided_exit_before_ruin_integral_identity X hX q hq W hW
        (a + ε) a hlevel ha.le hxa
    have hu : a + ε - a = ε := by ring
    simpa only [hu] using hcore
  exact chat12_upper_eventual_renewal_of_exit_factor
    X hX q hq W hW a ha hD hd hExit
