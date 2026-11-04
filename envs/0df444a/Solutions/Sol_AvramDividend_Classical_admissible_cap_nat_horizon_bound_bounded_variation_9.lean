-- Prove2me | solution 9 for AvramDividend.Classical.admissible_cap_nat_horizon_bound_bounded_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T06:45:26.00218+00:00
-- url     : https://prove2.me/submissions/c9fae56c-1d29-4bde-b46e-022ba5ceac1d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_zero_horizon_hjb_bound
import Theorems.Thm_AvramDividend_Classical_local_verification_stochastic_core_side_conditions
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_full_stieltjes_expected_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_clock_real_budget_to_ennreal
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_eq_inter
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- Source-exact natural-horizon cash bound through the positive-time terminal budget. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ n : ℕ, (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)), ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  intro n
  have hT : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hMain (T : ℝ) (hT : 0 ≤ T) :
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x) := by
    have hsmooth :
        (¬ X.BoundedVariation → ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
        (X.BoundedVariation → ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) := by
      constructor
      · intro hn; exact False.elim (hn hBV)
      · intro _; exact hw_smooth
    by_cases hT0 : T = 0
    · subst T
      exact admissible_cap_truncated_zero_horizon_hjb_bound
        X q x w C hw_cont hw0 hsmooth hw_hjb D hD hxc
    · have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
      obtain ⟨hgen, hgrad, hnonneg, hjump⟩ :=
        local_verification_stochastic_core_side_conditions
          X q w C hw_cont hw0 hsmooth hw_hjb x hxc D hD
      let S : ℝ≥0 := ⟨T, hT⟩
      let Term : Ω → ℝ := fun ω =>
        if (S : ℝ≥0∞) < ruinTime X x D ω then
          max 0 (Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω))
        else 0
      have hCore := avram_wave8_04_original_BV_positive_horizon_full_stieltjes_expected_budget
          X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
          hgen hgrad x hx hxc D hD hnonneg hjump T hT hTpos
      have hTermNonneg : ∀ ω, 0 ≤ Term ω := by intro ω; dsimp [Term]; split_ifs <;> simp
      have hMeanNonneg : 0 ≤ ∫ ω, Term ω ∂P := integral_nonneg hTermNonneg
      have hReal : (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) ≤
            w x := (le_add_of_nonneg_right hMeanNonneg).trans hCore
      exact avram_wave7_03_original_full_clock_real_budget_to_ennreal
        X x C D hD T hT q (w x) hReal
  have hFinite := hMain (n : ℝ) hT
  have hSub (ω : Ω) :
      paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ⊆
      paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ) := by
    intro t ht
    rw [paymentTimes_min_eq_inter] at ht
    rcases ht with ⟨hpay, hstop⟩
    refine ⟨hpay, ?_⟩
    change 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < (n : ℝ≥0∞)) at hstop
    rcases hstop.2 with hzero | hlt
    · change t ≤ (n : ℝ)
      rw [hzero]; exact hT
    · change t ≤ (n : ℝ)
      by_contra hnot
      have hnlt : (n : ℝ) < t := lt_of_not_ge hnot
      have heno : (n : ℝ≥0∞) ≤ ENNReal.ofReal t := by
        simpa only [ENNReal.ofReal_natCast] using (ENNReal.ofReal_le_ofReal hnlt.le)
      exact (not_lt_of_ge heno) hlt
  calc
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P)
      ≤ (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
          apply lintegral_mono
          intro ω; exact lintegral_mono_set (hSub ω)
    _ ≤ ENNReal.ofReal (w x) := hFinite
