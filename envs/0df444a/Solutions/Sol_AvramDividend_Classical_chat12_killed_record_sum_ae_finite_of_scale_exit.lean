-- Prove2me | solution 1 for AvramDividend.Classical.chat12_killed_record_sum_ae_finite_of_scale_exit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T20:41:25.217811+00:00
-- url     : https://prove2.me/submissions/983b3c81-a030-4d80-b7f4-865abaafa332

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_discount_reward_measurable
import Theorems.Thm_AvramDividend_Classical_chat12_total_expected_upper_scale_finite_of_exit
import Theorems.Thm_AvramDividend_Classical_chat12_expected_record_sum_finite_ae
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε)
    (hWright : 0 < W (a + ε)) (hWa : 0 ≤ W a)
    (hWinc : W a < W (a + ε))
    (hExit : (∫⁻ ω, if
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W a / W (a + ε))) :
    ∀ᵐ ω ∂P, (∑' n : ℕ,
      if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
      else 0) < ∞ := by
  let w : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
        barrierRuinTime X a ω then
      ENNReal.ofReal (ε * Real.exp
        (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
    else 0
  have hMeas : ∀ n : ℕ, Measurable (w n) := by
    intro n
    exact killed_firstRecord_discount_reward_measurable
      X a ((n : ℝ) * ε) ε q
  have hBound : (∑' n : ℕ, ∫⁻ ω, w n ω ∂P) < ∞ := by
    simpa only [w] using
      (chat12_total_expected_upper_scale_finite_of_exit
        X hX q hq W hW a ε ha hε hWright hWa hWinc hExit)
  have hAE := chat12_expected_record_sum_finite_ae P w hMeas hBound
  simpa only [w] using hAE
