-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_ubv_natural_future_clock_all_values
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:20:18.111659+00:00
-- url     : https://prove2.me/submissions/763ad7df-a116-4644-b4c0-17364a8b9c5e

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
/-- One future natural stopped clock for each integer observation horizon
    controls original UBV perpetual capped and unrestricted values. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hw0 : 0 ≤ w 0)
    (hNext : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
      ∀ (n : ℕ), 0 < x →
        ∃ m : ℕ, n < m ∧
          (∫⁻ ω, ∫⁻ t in paymentTimes
            (min (ruinTime X x D ω) (m : ℝ≥0∞)) ∩ Iic (n : ℝ),
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
      (by
        intro hxpos
        obtain ⟨m, hm, hCash⟩ := hNext x hx hxc D hD n hxpos
        exact ⟨m, (by exact_mod_cast hm), hCash⟩)
  refine And.intro hCap ?_
  intro hTop x hx
  subst C
  simpa only [valueFunctionLe_top_eq_valueFunction] using
    hCap x hx le_top
