-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_le_right_scale_quotient_of_killed_grid_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:31:06.835641+00:00
-- url     : https://prove2.me/submissions/384c53f6-c2f8-4b7c-980b-ea1b0e643b5b

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_chat08_record_grid_stopped_weights_aemeasurable
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_grid_geometric_expected_upper_of_step
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_le_right_scale_quotient_of_record_budgets
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (W : ℝ → ℝ) (a b q ε : ℝ)
    (hq : 0 ≤ q) (hε : 0 < ε)
    (hWright : 0 < W (a + ε)) (hWa : 0 ≤ W a)
    (hWinc : W a < W (a + ε))
    (w : ℕ → Ω → ℝ≥0∞)
    (hw : ∀ n ω, w n ω =
      if twoSidedExitUpTime X (b + (n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (ε * Real.exp (-(q * (twoSidedExitUpTime X (b + (n : ℝ) * ε) ω).toReal)))
      else 0)
    (hbudget : ∀ᵐ ω ∂P,
      (∫⁻ t,
        if t ∈ paymentTimes (barrierRuinTime X a ω)
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ≤ (∑' n, w n ω))
    (hstep : ∀ n,
      (∫⁻ ω, w (n + 1) ω ∂P) ≤
        ENNReal.ofReal (W a / W (a + ε)) *
          (∫⁻ ω, w n ω ∂P)) :
    barrierSupValue X a q ≤
      ENNReal.ofReal (ε * W (a + ε) / (W (a + ε) - W a)) := by
  have hmeas : ∀ n : ℕ, AEMeasurable (w n) P := by
    intro n
    have hfun : w n = (fun ω : Ω =>
        if twoSidedExitUpTime X (b + (n : ℝ) * ε) ω <
            barrierRuinTime X a ω then
          ENNReal.ofReal
            (ε * Real.exp (-(q * (twoSidedExitUpTime X (b + (n : ℝ) * ε) ω).toReal)))
        else 0) := funext (hw n)
    rw [hfun]
    exact (chat08_record_grid_stopped_weights_aemeasurable X a b q ε id) n
  have hratio : 0 ≤ W a / W (a + ε) :=
    div_nonneg hWa (le_of_lt hWright)
  have hgeom : ∀ n, (∫⁻ ω, w n ω ∂P) ≤
      ENNReal.ofReal (ε * (W a / W (a + ε)) ^ n) :=
    killed_firstRecord_grid_geometric_expected_upper_of_step
      X a b q ε (W a / W (a + ε)) hq (le_of_lt hε)
      hratio w hw hstep
  exact barrierSupValue_le_right_scale_quotient_of_record_budgets
    X W a q ε (le_of_lt hε) hWright hWa hWinc
    w hmeas hbudget hgeom
