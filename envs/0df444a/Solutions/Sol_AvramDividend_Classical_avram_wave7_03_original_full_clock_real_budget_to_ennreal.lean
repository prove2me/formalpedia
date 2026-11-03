-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_full_clock_real_budget_to_ennreal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T11:42:18.580058+00:00
-- url     : https://prove2.me/submissions/5b6ef9e3-3507-48ac-bb45-b881c694f1ba

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_real_horizon_full_stieltjes_reward_integrable_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_real_horizon_stopped_full_stieltjes_payment_ae_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The true original Stieltjes cash L¹ and almost-sure finiteness
    transfer any full finite-clock real mean bound to the ENNReal budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (q B : ℝ)
    (hRealBudget :
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal B := by
  let F : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)
  have hInt : Integrable (fun ω : Ω => (F ω).toReal) P := by
    simpa only [F] using
      (avram_wave5_03_original_real_horizon_full_stieltjes_reward_integrable_L1
        X x C D hD T hT q)
  have hFinite : ∀ᵐ ω ∂P, F ω < ⊤ := by
    simpa only [F] using
      (avram_wave5_03_original_real_horizon_stopped_full_stieltjes_payment_ae_finite
        X x C D hD T hT q)
  have hEmbed : (fun ω : Ω => ENNReal.ofReal ((F ω).toReal)) =ᵐ[P] F := by
    filter_upwards [hFinite] with ω hω
    exact ENNReal.ofReal_toReal (ne_of_lt hω)
  have hCash :
      ENNReal.ofReal (∫ ω, (F ω).toReal ∂P) =
        ∫⁻ ω, F ω ∂P := by
    calc
      ENNReal.ofReal (∫ ω, (F ω).toReal ∂P) =
          ∫⁻ ω, ENNReal.ofReal ((F ω).toReal) ∂P := by
            apply MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
            exact Filter.Eventually.of_forall
              (fun ω : Ω => ENNReal.toReal_nonneg)
      _ = ∫⁻ ω, F ω ∂P := lintegral_congr_ae hEmbed
  change (∫⁻ ω, F ω ∂P) ≤ ENNReal.ofReal B
  rw [← hCash]
  exact ENNReal.ofReal_le_ofReal (by simpa only [F] using hRealBudget)
