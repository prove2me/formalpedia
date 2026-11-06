-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_ubv_zero_reserve_full_root_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:08:06.152889+00:00
-- url     : https://prove2.me/submissions/da86028d-362f-42d3-899a-5ec53ef466e6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_ubv_original_zero_capital_exact_zero_reward_and_value
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_top_eq_valueFunction
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_ubv_vcstar_zero_reserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/- A true zero-reserve root equality for every original cap, including top,
   with no c-star smoothness or positive-reserve stochastic assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    (∀ C : ℝ≥0∞,
      valueFunctionLe X q C 0 = ENNReal.ofReal (vcstar W 0)) ∧
    valueFunction X q 0 = ENNReal.ofReal (vcstar W 0) := by
  have hv : vcstar W 0 = 0 :=
    avram_sweep16_ubv_vcstar_zero_reserve X hBV q hq W hW
  have hAll : ∀ C : ℝ≥0∞, valueFunctionLe X q C 0 = 0 :=
    fun C => (avram_wave6_10_ubv_original_zero_capital_exact_zero_reward_and_value
      X hBV q C).2
  constructor
  · intro C
    simpa only [hv, ENNReal.ofReal_zero] using hAll C
  · have hTop := hAll (⊤ : ℝ≥0∞)
    simpa only [valueFunctionLe_top_eq_valueFunction, hv,
      ENNReal.ofReal_zero] using hTop
