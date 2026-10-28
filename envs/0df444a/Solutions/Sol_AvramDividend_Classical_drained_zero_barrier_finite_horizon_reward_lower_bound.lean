-- Prove2me | solution 1 for AvramDividend.Classical.drained_zero_barrier_finite_horizon_reward_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:48:39.421647+00:00
-- url     : https://prove2.me/submissions/a4b3526f-df37-49d8-88c9-e13e2ad87061

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_drained_zero_barrier_truncated_zero_reward_eq_initial_capital
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The initial atom is included in every nonnegative finite-horizon
    dividend reward, even when ruin occurs immediately afterwards. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x)
    (q T : ℝ) (hT : 0 ≤ T) (ω : Ω) :
    ENNReal.ofReal x ≤
      (∫⁻ t in paymentTimes
          (ruinTime X x
            (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure
              (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) ω)) := by
  let D : ℝ≥0 → Ω → ℝ :=
    fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)
  have hzero :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
          ENNReal.ofReal x := by
    simpa only [D] using
      (drained_zero_barrier_truncated_zero_reward_eq_initial_capital
        X x hx q (ruinTime X x D ω) ω)
  have hsubset :
      paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ) ⊆
        paymentTimes (ruinTime X x D ω) ∩ Iic T := by
    intro t ht
    exact ⟨ht.1, le_trans ht.2 hT⟩
  change ENNReal.ofReal x ≤
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
  calc
    ENNReal.ofReal x =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) :=
      hzero.symm
    _ ≤ _ := lintegral_mono_set hsubset
