-- Prove2me | solution 8 for AvramDividend.Classical.avram_p4_f4_mixed_gaussian_jump_top_cap_ennreal_expected_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T09:40:24.475615+00:00
-- url     : https://prove2.me/submissions/614771f9-0317-46a7-bb6b-98b5c745995e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_fatou_physical_clock_construction
import Theorems.Thm_AvramDividend_Classical_avram_p4_f11_original_ubv_nonzero_gaussian_compensated_signed_budget
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_three_compensators_signed_remainder_auto_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_rightcont_stopping_zero_mask_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f8_original_exact_clock_zero_reward_le_initial
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_ae_natural_clock_fatou_L1_budget
import Theorems.Thm_AvramDividend_Classical_avram_limit2_integrable_nonnegative_real_grid_to_ennreal_budget
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_natural_clock_three_signs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (hTop : C = ⊤) :
    (∫⁻ ω, ENNReal.ofReal (Term ω + Cash ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨σ, F, hwx, hσstop, hσle, hFsource, hFm, hFI, hFn, hFconv⟩ :=
    avram_p4_f4_original_fatou_physical_clock_construction
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen
      hw_grad x hx hxc D hD hw_nonneg hjump n hn τ
      hτeq hτmeas hτstop W Cash Term hW hCash hTerm hTermMeas hCashI
  obtain ⟨_, hTermNonneg, hCashNonneg⟩ :=
    avram_p4_f4_original_natural_clock_three_signs
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen
      hw_grad x hx hxc D hD hw_nonneg hjump n hn τ
      hτeq hτmeas hτstop W Cash Term hW hCash hTerm hTermMeas hCashI
  have hSmeas : AEStronglyMeasurable (fun ω => Term ω + Cash ω) P :=
    hTermMeas.add hCashI.aestronglyMeasurable
  have hSnonneg : 0 ≤ᵐ[P] (fun ω => Term ω + Cash ω) := by
    filter_upwards [hTermNonneg, hCashNonneg] with ω ht hc
    exact add_nonneg ht hc
  have hFb : ∀ k, (∫ ω, F k ω ∂P) ≤ w x := by
    intro k
    obtain ⟨Mc, Ms, Ml, G, R, hMcI, hMsI, hMlI,
        hMc0, hMs0, hMl0, hG, hR, hIto⟩ :=
      avram_p4_f11_original_ubv_nonzero_gaussian_compensated_signed_budget
        X hX hBV hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen
        hw_grad x hx hxc D hD hw_nonneg hjump n hn τ
        hτeq hτmeas hτstop W Cash Term hW hCash hTerm hTermMeas hCashI
        σ F hσstop hσle hFsource hFI k
    have hMI : Integrable (fun ω => if σ k ω = 0 then w x else F k ω) P :=
      avram_ubv_loc6_rightcont_stopping_zero_mask_integrable
        (σ k) (hσstop k) (F k) (hFI k) (w x)
    have hMN : 0 ≤ᵐ[P] (fun ω => if σ k ω = 0 then w x else F k ω) := by
      filter_upwards [hFn k] with ω hf
      split_ifs with hk
      · exact hwx
      · exact hf
    obtain ⟨_, hMasked⟩ :=
      avram_ubv_loc6_three_compensators_signed_remainder_auto_L1
        (fun ω => if σ k ω = 0 then w x else F k ω)
        Mc Ms Ml G R (w x)
        hMI.aestronglyMeasurable hMN hMcI hMsI hMlI
        hMc0 hMs0 hMl0 hG hR hIto
    have hLe : ∀ ω, F k ω ≤ if σ k ω = 0 then w x else F k ω := by
      intro ω
      split_ifs with hk
      · exact avram_p4_f8_original_exact_clock_zero_reward_le_initial
          X x q w C D hD hjump σ F hFsource k ω hk
      · exact le_rfl
    exact (integral_mono (hFI k) hMI hLe).trans hMasked
  obtain ⟨hSI, hMean⟩ :=
    avram_p4_f4_ae_natural_clock_fatou_L1_budget
      P (fun ω => Term ω + Cash ω) F
      hSmeas hSnonneg hFm hFI hFn hFconv (w x) hwx hFb
  have hBudget :=
    avram_limit2_integrable_nonnegative_real_grid_to_ennreal_budget
      (fun _ : ℕ => (fun ω => Term ω + Cash ω)) (w x)
      (fun _ => hSI) (fun _ => hSnonneg) (fun _ => hMean) 0
  simpa using hBudget
