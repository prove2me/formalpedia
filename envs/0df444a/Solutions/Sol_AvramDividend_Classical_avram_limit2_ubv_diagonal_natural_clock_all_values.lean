-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_ubv_diagonal_natural_clock_all_values
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:31:55.912805+00:00
-- url     : https://prove2.me/submissions/bb674192-70ea-4af2-a713-dda3b4e4c22d

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
/-- Uniform diagonal natural ruin-clock cash bounds yield original UBV
    perpetual capped and unrestricted values without terminal vanishing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hw0 : 0 ≤ w 0)
    (hDiag : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ (D : ℝ≥0 → Ω → ℝ), IsAdmissibleLe X x C D →
      ∀ (m : ℕ), 0 < x →
          (∫⁻ ω, ∫⁻ t in paymentTimes
            (min (ruinTime X x D ω) (m : ℝ≥0∞)) ∩ Iic (m : ℝ),
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
        refine Exists.intro (n + 1) (And.intro ?_ ?_)
        · exact_mod_cast Nat.lt_succ_self n
        · refine le_trans ?_ (hDiag x hx hxc D hD (n + 1) hxpos)
          apply lintegral_mono
          intro ω
          apply lintegral_mono_set
          intro t ht
          have hn : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
            exact_mod_cast Nat.le_succ n
          exact ⟨ht.1, le_trans ht.2 hn⟩)
  refine And.intro hCap ?_
  intro hTop x hx
  subst C
  simpa only [valueFunctionLe_top_eq_valueFunction] using
    hCap x hx le_top
