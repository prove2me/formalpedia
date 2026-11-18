-- Prove2me | solution 13 for AvramDividend.Classical.avram_wave7_04_original_BV_complement_real_stieltjes_HJB_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T23:26:48.817726+00:00
-- url     : https://prove2.me/submissions/c367585e-28e6-4cd9-9cbf-7f6633e3132c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb38_original_finitecap_C1_slope_candidate_affine_reserve_floor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_gradient_linear_lower_envelope
import Theorems.Thm_AvramDividend_Classical_avram_bv_topcap_original_full_T_strict_cash_expected_budget
import Theorems.Thm_AvramDividend_Classical_avram_a19_finite_cap_original_full_T_HJB_source
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_strict_expected_to_full_atom_ennreal
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_full_cash_and_survival_terminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_bva36_finite_lintegral_budget_to_real_integral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T)
    (hEnvelope : ¬ (x + T * X.drift ≤ w x)) :
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P) ≤
      w x := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hxw : x ≤ w x := by
    by_cases htop : C = ⊤
    · have hxCap : ENNReal.ofReal x < C := by
        simp [htop]
      have hFloor :=
        (avram_wave7_02_original_positive_cap_C1_gradient_linear_lower_envelope
          C hC w hw_cont hw_smooth hw_grad x hx hxCap) x
          (by simp [hx])
      linarith
    · have hxCap : x ≤ C.toReal :=
        (ENNReal.ofReal_le_iff_le_toReal htop).mp hxc
      have hFloor :=
        avram_bvb38_original_finitecap_C1_slope_candidate_affine_reserve_floor
          C hC htop w hw_cont hw_smooth hw_grad x hx hxCap
      linarith
  have hwx : 0 ≤ w x := hx.trans hxw
  have hTpos : 0 < T := by
    by_contra h
    have h0 : T = 0 := le_antisymm (le_of_not_gt h) hT
    exact hEnvelope (by simpa [h0] using hxw)
  let S : ℝ≥0 := ⟨T, hT⟩
  have hStrict :
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0) ∂P) ≤ w x := by
    by_cases htop : C = ⊤
    · simpa only [S] using
        (avram_bv_topcap_original_full_T_strict_cash_expected_budget
          X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
          hw_grad x hx hxc D hD hw_nonneg hjump T hT hTpos htop)
    · simpa only [S] using
        (avram_a19_finite_cap_original_full_T_HJB_source
          X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
          hw_grad x hx hxc D hD hw_nonneg hjump T hT hTpos htop)
  let f : Ω → ℝ≥0∞ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
  have hFinite (ω : Ω) : f ω ≠ ⊤ := by
    have hDiv : IsDividendStrategy 𝓕 D := hD.1.1
    have hMass :
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) < ⊤ := by
      simpa only [show (S : ℝ) = T from rfl] using
        (avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
          D hDiv ω (ruinTime X x D ω) S q hq.le)
    exact ne_of_lt hMass
  have hFI : Integrable (fun ω => (f ω).toReal) P := by
    simpa only [f] using
      (avram_wave8_04_original_BV_full_cash_and_survival_terminal_L1
        X hBV q w hw_cont hw_neg x C D hD T hT).1
  have hBudget : (∫⁻ ω, f ω ∂P) ≤ ENNReal.ofReal (w x) := by
    simpa only [f] using
      (avram_bv_env3_original_strict_expected_to_full_atom_ennreal
        X hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
        x hx hxc D hD hjump T hT hTpos (by simpa only [S] using hStrict))
  exact avram_bva36_finite_lintegral_budget_to_real_integral
    P f (w x) hFinite hFI hwx hBudget
