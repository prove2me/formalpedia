-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_positive_reserve_high_barrier_value_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T20:42:53.109014+00:00
-- url     : https://prove2.me/submissions/68c6c071-9d55-43f0-8534-d541ed46e34f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_positive_reserve_exp_dividend_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- With positive initial capital, the original genuine reflected barrier
dividend value vanishes when the payout threshold tends to infinity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 < x) :
    Tendsto (fun a : ℝ => dividendValue X q x (barrierStrategy X x a))
      atTop (𝓝 (0 : ENNReal)) := by
  obtain ⟨φ, C, hφ, hC, hbound⟩ :=
    avram_wave3_02_positive_reserve_exp_dividend_bound X hX q hq W hW
  have hlin : Tendsto (fun a : ℝ => a * (-φ)) atTop atBot :=
    Filter.Tendsto.atTop_mul_const_of_neg (by linarith : -φ < 0) tendsto_id
  have hshift : Tendsto (fun a : ℝ => a * (-φ) + φ * x) atTop atBot :=
    Filter.tendsto_atBot_add_const_right atTop (φ * x) hlin
  have hexp : Tendsto (fun a : ℝ => Real.exp (-φ * (a - x)))
      atTop (𝓝 (0 : ℝ)) := by
    have heq : (fun a : ℝ => Real.exp (-φ * (a - x))) =
        (fun a : ℝ => Real.exp (a * (-φ) + φ * x)) := by
      funext a
      congr 1
      ring
    rw [heq]
    exact Real.tendsto_exp_atBot.comp hshift
  have hreal : Tendsto (fun a : ℝ => Real.exp (-φ * (a - x)) * C)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using hexp.mul_const C
  have hupper : Tendsto (fun a : ℝ =>
      ENNReal.ofReal (Real.exp (-φ * (a - x)) * C))
      atTop (𝓝 (0 : ENNReal)) := by
    have ht := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
    change Tendsto (fun a : ℝ =>
      ENNReal.ofReal (Real.exp (-φ * (a - x)) * C))
      atTop (𝓝 (ENNReal.ofReal (0 : ℝ))) at ht
    simpa only [ENNReal.ofReal_zero] using ht
  have hevent : ∀ᶠ a : ℝ in atTop,
      dividendValue X q x (barrierStrategy X x a) ≤
        ENNReal.ofReal (Real.exp (-φ * (a - x)) * C) := by
    filter_upwards [eventually_ge_atTop x] with a ha
    rw [ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
    exact hbound x a hx ha
  exact Filter.Tendsto.squeeze'
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ENNReal)) atTop (𝓝 0))
    hupper (Filter.Eventually.of_forall
      (fun a => (show (0 : ENNReal) ≤
        dividendValue X q x (barrierStrategy X x a) from zero_le))) hevent
