-- Prove2me | solution 2 for AvramDividend.Classical.barrierSupValue_stopped_renewal_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T07:21:24.630345+00:00
-- url     : https://prove2.me/submissions/06411608-2dbe-4b3b-b149-8f4b6d18d8bd

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_two_sided_exit_before_ruin_integral_identity
import Theorems.Thm_AvramDividend_Classical_chat12_lower_eventual_renewal_of_exit_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Lower reflected reward bound from the raw two-sided-exit integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a : ℝ) (ha : 0 < a)
    (hD : HasDerivAt W (deriv W a) a) (hd : deriv W a ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (ε * W (a - ε) / (W a - W (a - ε))) ≤
        barrierSupValue X a q := by
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε := by
    change Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ)
    exact self_mem_nhdsWithin
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < a := by
    exact (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds
  have hExit : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W (a - ε) / W a) := by
    filter_upwards [hpos, hsmall] with ε hε hεa
    have hx0 : 0 ≤ a - ε := by linarith
    have hxa : a - ε ≤ a := by linarith
    have hcore :=
      two_sided_exit_before_ruin_integral_identity X hX q hq W hW
        a (a - ε) ha hx0 hxa
    have hu : a - (a - ε) = ε := by ring
    have hl : -(a - ε) = ε - a := by ring
    simpa only [hu, hl] using hcore
  exact chat12_lower_eventual_renewal_of_exit_factor
    X hX q hq W hW a ha hD hd hExit
