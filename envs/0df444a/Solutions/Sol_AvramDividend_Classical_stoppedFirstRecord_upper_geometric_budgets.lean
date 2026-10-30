-- Prove2me | solution 1 for AvramDividend.Classical.stoppedFirstRecord_upper_geometric_budgets
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:25:17.095983+00:00
-- url     : https://prove2.me/submissions/922eadc9-7a16-45e9-a01a-434a373197df

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_barrierSup_stopped_indicator_reward_le_killed_record_tsum
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_one_step_scale_regeneration_upper

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-! Reduce the true upper geometric budget to its killed-record Markov step. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a ε : ℝ) (ha : 0 < a)
    (hε : 0 < ε)
    (hWright : 0 < W (a + ε)) (hWa : 0 ≤ W a)
    (hWinc : W a < W (a + ε)) :
    ∃ w : ℕ → Ω → ℝ≥0∞,
      (∀ n ω, w n ω =
        if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
            barrierRuinTime X a ω then
          ENNReal.ofReal
            (ε * Real.exp (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
        else 0)
      ∧ (∀ᵐ ω ∂P,
        (∫⁻ t,
          if t ∈ paymentTimes (barrierRuinTime X a ω)
          then ENNReal.ofReal (Real.exp (-(q * t))) else 0
          ∂(dividendMeasure (runningSup X) ω)) ≤ (∑' n, w n ω))
      ∧ (∀ n : ℕ,
        (∫⁻ ω, w (n + 1) ω ∂P) ≤
          ENNReal.ofReal (W a / W (a + ε)) *
            (∫⁻ ω, w n ω ∂P)) := by
  classical
  let w : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
        barrierRuinTime X a ω then
      ENNReal.ofReal
        (ε * Real.exp (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
    else 0
  refine ⟨w, ?_, ?_, ?_⟩
  · intro n ω
    rfl
  · apply Filter.Eventually.of_forall
    intro ω
    simpa only [w] using
      barrierSup_stopped_indicator_reward_le_killed_record_tsum
        X a q ε (le_of_lt hq) hε ω
  · intro n
    simpa only [w] using
      killed_firstRecord_one_step_scale_regeneration_upper
        X hX q hq W hW a ε ha hε hWright hWa hWinc n
