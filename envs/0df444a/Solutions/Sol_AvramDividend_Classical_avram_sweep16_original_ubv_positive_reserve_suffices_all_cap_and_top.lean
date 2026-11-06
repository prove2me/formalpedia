-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_original_ubv_positive_reserve_suffices_all_cap_and_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:05:15.294168+00:00
-- url     : https://prove2.me/submissions/90f11bb5-5484-4005-b051-a13eed92865c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_original_ubv_zero_reserve_uniform_all_caps
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_top_eq_valueFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/- A positive-reserve verification budget suffices for every reserve in the
   original UBV model; the zero boundary and top cap are already certified. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (q : ℝ)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0) (C : ℝ≥0∞)
    (hPositive : ∀ x : ℝ, 0 < x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by
  have hAll : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x) := by
    intro x hx hxc
    by_cases hx0 : x = 0
    · subst x
      exact (avram_sweep16_original_ubv_zero_reserve_uniform_all_caps
        X hBV q w hw0).1 C
    · exact hPositive x (lt_of_le_of_ne hx (Ne.symm hx0)) hxc
  refine ⟨hAll, ?_⟩
  intro hC
  subst C
  intro x hx
  simpa only [valueFunctionLe_top_eq_valueFunction] using
    hAll x hx le_top
