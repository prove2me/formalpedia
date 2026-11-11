-- Prove2me | solution 8 for AvramDividend.Classical.avram_wave7_04_original_BV_complement_real_stieltjes_HJB_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T18:09:58.801498+00:00
-- url     : https://prove2.me/submissions/08de2a75-5f4e-4128-a13a-a3d08924c0d1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
import Theorems.Thm_AvramDividend_Classical_avram_a19_physical_strict_horizon_uniform_grid
import Theorems.Thm_AvramDividend_Classical_avram_rr7_original_BV_drift_dropped_positive_error_uniform_grid
import Theorems.Thm_AvramDividend_Classical_avram_bv_route11_drift_discarded_real_to_closed_cash
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_real_horizon_full_stieltjes_reward_integrable_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_real_horizon_stopped_full_stieltjes_payment_ae_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
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
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ∂P)
      ≤ w x := by
  have hTpos : 0 < T :=
    (avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
      X hX hBV q hq w C hC hw_cont hw0 hw_smooth hw_grad
      x hx hxc D hD T hT hEnvelope).1
  obtain ⟨u, hgrid, hmono, huniform⟩ :=
    avram_a19_physical_strict_horizon_uniform_grid T hTpos
  obtain ⟨M, Err, hM, hErrInt, hErrMean, hErrBound⟩ :=
    avram_rr7_original_BV_drift_dropped_positive_error_uniform_grid
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hTpos
      u hgrid hmono huniform
  have hDiscard :
      let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
      let S : ℝ≥0 := ⟨T, le_of_lt hTpos⟩
      ∃ M Err : ℕ → Ω → ℝ,
        (∀ n, Integrable (M n) P ∧ (∫ ω, M n ω ∂P) ≤ 0) ∧
        (∀ n, Integrable (fun ω => max (Err n ω) 0) P) ∧
        Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (nhds 0) ∧
        (∀ n, ∀ᵐ ω ∂P,
          (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
            ENNReal.ofReal (Real.exp (-(q * t)))
              ∂(dividendMeasure D ω)).toReal +
            (if (S : ℝ≥0∞) < ruinTime X x D ω then
              Real.exp (-(q * T)) * w (riskProcess X x D S ω)
            else 0) ≤
          w x + M n ω + max (Err n ω) 0) := by
    dsimp
    refine ⟨M, Err, ?_, hErrInt, hErrMean, ?_⟩
    · exact fun n => ⟨(hM n).1, le_of_eq (hM n).2⟩
    · exact hErrBound
  have hCashEnn :=
    avram_bv_route11_drift_discarded_real_to_closed_cash
      X hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_grad x hx hxc D hD hjump T hTpos hDiscard
  let G : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  have hGint : Integrable (fun ω => (G ω).toReal) P :=
    avram_wave5_03_original_real_horizon_full_stieltjes_reward_integrable_L1
      X x C D hD T hT q
  have hGfinite : ∀ᵐ ω ∂P, G ω < ⊤ :=
    avram_wave5_03_original_real_horizon_stopped_full_stieltjes_payment_ae_finite
      X x C D hD T hT q
  have hGnonneg : 0 ≤ᵐ[P] (fun ω => (G ω).toReal) :=
    Filter.Eventually.of_forall (fun ω => ENNReal.toReal_nonneg)
  have hGeo : (fun ω => ENNReal.ofReal (G ω).toReal) =ᵐ[P] G :=
    hGfinite.mono (fun ω hω => ENNReal.ofReal_toReal (ne_of_lt hω))
  have hRealEq :
      (∫ ω, (G ω).toReal ∂P) = (∫⁻ ω, G ω ∂P).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae hGnonneg hGint.aestronglyMeasurable]
    exact congrArg ENNReal.toReal (lintegral_congr_ae hGeo)
  have hWlower : w 0 + x ≤ w x :=
    avram_wave7_02_original_closed_cap_C1_gradient_linear_lower_envelope
      C hC w hw_cont hw_smooth hw_grad x hx hxc x ⟨hx, le_refl x⟩
  have hWnonneg : 0 ≤ w x := by linarith
  have hRealLe :
      (∫⁻ ω, G ω ∂P).toReal ≤ w x := by
    have h := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hCashEnn
    simpa only [ENNReal.toReal_ofReal hWnonneg] using h
  exact hRealEq.trans_le hRealLe
