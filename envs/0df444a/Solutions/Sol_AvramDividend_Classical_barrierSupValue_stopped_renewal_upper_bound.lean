-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_stopped_renewal_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:19:05.713018+00:00
-- url     : https://prove2.me/submissions/6358f9e5-7872-4cca-b0b6-ece15a6682fe

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Order.OrderClosed
import Theorems.Thm_AvramDividend_Classical_stoppedFirstRecord_upper_geometric_budgets
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_stopped_renewal_upper_of_eventual_killed_record_step
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_monotone_nonzero_derivative_eventually_right_increment
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal Topology Classical

/-! Close the stopped upper bound from the genuine killed-grid budget package. -/
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
  classical
  let w : ℝ → ℕ → Ω → ℝ≥0∞ := fun ε n ω =>
    if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
        barrierRuinTime X a ω then
      ENNReal.ofReal
        (ε * Real.exp (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
    else 0
  have hWa : 0 < W a :=
    scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  have hinc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), W a < W (a + ε) :=
    monotone_nonzero_derivative_eventually_right_increment W a
      (scaleFunction_monotone X q W hW) hD hd
  have heps : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hε
  have hpair : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∀ᵐ ω ∂P,
        (∫⁻ t,
          if t ∈ paymentTimes (barrierRuinTime X a ω)
          then ENNReal.ofReal (Real.exp (-(q * t))) else 0
          ∂(dividendMeasure (runningSup X) ω)) ≤ (∑' n, w ε n ω))
      ∧ (∀ n : ℕ,
        (∫⁻ ω, w ε (n + 1) ω ∂P) ≤
          ENNReal.ofReal (W a / W (a + ε)) *
            (∫⁻ ω, w ε n ω ∂P)) := by
    filter_upwards [hinc, heps] with ε hincε hε
    obtain ⟨v, hv, hbudget, hstep⟩ :=
      stoppedFirstRecord_upper_geometric_budgets X hX q hq W hW a ε
        ha hε (lt_trans hWa hincε) (le_of_lt hWa) hincε
    have hweq : v = w ε := by
      funext n ω
      exact hv n ω
    constructor
    · simpa only [hweq] using hbudget
    · simpa only [hweq] using hstep
  apply barrierSupValue_stopped_renewal_upper_of_eventual_killed_record_step
    X hX q hq W hW a ha hD hd w
  · exact Filter.Eventually.of_forall (fun ε n ω => rfl)
  · exact hpair.mono (fun ε h => h.1)
  · exact hpair.mono (fun ε h => h.2)
