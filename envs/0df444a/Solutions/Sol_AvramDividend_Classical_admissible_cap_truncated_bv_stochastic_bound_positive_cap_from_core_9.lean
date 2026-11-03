-- Prove2me | solution 9 for AvramDividend.Classical.admissible_cap_truncated_bv_stochastic_bound_positive_cap_from_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:33:02.163687+00:00
-- url     : https://prove2.me/submissions/fc67d686-47b1-4446-9d09-dfd078f9158d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_allCap_admissible_initial_capital_nonneg
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_separate_gradient_right_atom_control
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_initial_state
import Theorems.Thm_AvramDividend_Classical_truncated_zero_horizon_bound_of_initial_jump_secant
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_complete_closed_horizon_sharp_expected_drift_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave7_04_original_BV_complement_real_stieltjes_HJB_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_clock_real_budget_to_ennreal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω))
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  classical
  have hx : 0 ≤ x := avram_wave3_04_allCap_admissible_initial_capital_nonneg
    X x C hxc D hD
  have hSplit :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :=
    ⟨fun hn => False.elim (hn hBV), fun _ => hw_smooth⟩
  have hAtom := avram_wave5_03_original_separate_gradient_right_atom_control
    X w C hC hw_cont hSplit hw_grad x hxc D hD
  by_cases hTzero : T = 0
  · subst T
    have hs : IsDividendStrategy 𝓕 D := hD.1.1
    have hjump : ∀ ω,
        rightLimit D 0 ω - D 0 ω ≤
          w x - w (x - (rightLimit D 0 ω - D 0 ω)) := by
      intro ω
      have hz : D 0 ω = 0 := hs.1 ω
      have hXz : X.X 0 ω = 0 := X.X_zero ω
      have h := hAtom ω 0 (Or.inl rfl)
      simpa [riskProcess, hz, hXz] using h
    have hpost : ∀ ω, 0 ≤ w (x - (rightLimit D 0 ω - D 0 ω)) := by
      intro ω
      obtain ⟨hnonneg, hcap⟩ := capped_postPaymentReserve_initial_state
        X x C D hD hxc ω
      have hsec := avram_wave3_03_bv_full_cap_gradient_secant
        C hC w hw_cont hw_smooth hw_grad 0 (x + X.X 0 ω - rightLimit D 0 ω)
        (le_refl (0 : ℝ)) hnonneg hcap
      have hw : 0 ≤ w (x + X.X 0 ω - rightLimit D 0 ω) := by linarith
      have hz : D 0 ω = 0 := hs.1 ω
      have hXz : X.X 0 ω = 0 := X.X_zero ω
      simpa [hz, hXz] using hw
    exact truncated_zero_horizon_bound_of_initial_jump_secant
      X q x w D hs hjump hpost
  · by_cases hEnvelope : x + T * X.drift ≤ w x
    · let S : ℝ≥0 := ⟨T, hT⟩
      have hRaw :=
        avram_wave3_03_bv_complete_closed_horizon_sharp_expected_drift_budget
          X hX hBV x hx C hxc D hD q (le_of_lt hq) S
      have hCoe : (S : ℝ) = T := rfl
      rw [hCoe] at hRaw
      exact hRaw.trans (ENNReal.ofReal_le_ofReal hEnvelope)
    · have hRealBudget :=
        avram_wave7_04_original_BV_complement_real_stieltjes_HJB_budget
          X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
          hw_gen hw_grad x hx hxc D hD hw_nonneg hAtom T hT hEnvelope
      exact avram_wave7_03_original_full_clock_real_budget_to_ennreal
        X x C D hD T hT q (w x) hRealBudget