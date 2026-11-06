-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_ubv_one_future_clock_uniform_cap_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:57:40.569202+00:00
-- url     : https://prove2.me/submissions/6f138c30-c3de-414c-91fb-be5effa5229c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_minimal_original_ubv_one_clock_value_bridge
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_positive_integer_horizon_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_limit2_closed_strict_original_cash_suprema_agree
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_top_eq_valueFunction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- For the true original UBV process, one future natural stopped-clock
    budget per closed horizon suffices for all perpetual capped values. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hw0 : 0 ≤ w 0)
    (hFuture : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
      ∀ (T : ℝ) (hT : 0 ≤ T), 0 < x →
        ∃ n : ℕ, T < (n : ℝ) ∧
          (∫⁻ ω, ∫⁻ t in paymentTimes
            (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
            ENNReal.ofReal (w x)) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by
  have hCap : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x) := by
    intro x hx hxc
    unfold valueFunctionLe
    refine iSup_le fun D => iSup_le fun hD => ?_
    rw [avram_limit2_original_strict_positive_integer_horizon_exhaustion
      X q x D hD.1]
    rw [← avram_limit2_closed_strict_original_cash_suprema_agree
      X q x D hD.1]
    refine iSup_le fun n => ?_
    exact avram_wave7_11_minimal_original_ubv_one_clock_value_bridge
      X hBV q w C hw0 x hx D hD (n : ℝ) (by positivity)
      (hFuture x hx hxc D hD (n : ℝ) (by positivity))
  refine And.intro hCap ?_
  intro hTop x hx
  subst C
  simpa only [valueFunctionLe_top_eq_valueFunction] using
    hCap x hx le_top
