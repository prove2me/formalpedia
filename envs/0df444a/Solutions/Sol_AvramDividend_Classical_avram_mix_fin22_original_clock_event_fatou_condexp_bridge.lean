-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin22_original_clock_event_fatou_condexp_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T10:25:23.406807+00:00
-- url     : https://prove2.me/submissions/08dae1c3-3a09-4a85-b12d-e21467b27355

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin19_original_spatial_reward_eventwise_fatou_from_exact_cofinal
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_any_clock_exact_closed_payoff_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_zero_clock_exact_physical_F_le
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_initial_event_positive_clock_partition
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite14_initial_event_budget_to_condexp
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C) (hwx : 0 ≤ w x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, (σ ω : ℝ≥0∞) ≤ (n : ℝ≥0∞))
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
              (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P)
    (S : ℕ → Ω → ℝ≥0∞)
    (hSmono : ∀ ω, Monotone (fun k => S k ω))
    (hSsup : ∀ᵐ ω ∂P, (⨆ k : ℕ, S k ω) = ⊤)
    (σk : ℕ → Ω → ℝ≥0)
    (hσk : ∀ k ω, σk k ω = (min (σ ω : ℝ≥0∞) (S k ω)).toNNReal)
    (hσmeas : Measurable σ) (hσkmeas : ∀ k, Measurable (σk k))
    (hσkle : ∀ k ω, σk k ω ≤ σ ω)
    (Fk : ℕ → Ω → ℝ)
    (hFksource : ∀ k ω, Fk k ω =
      Real.exp (-(q * (σk k ω : ℝ))) *
        w (if σk k ω = 0 ∨
              (σk k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σk k ω) ω - rightLimit D (σk k ω) ω
          else riskProcess X x D (σk k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σk k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hFkmeas : ∀ k, Measurable (Fk k)) (hFkint : ∀ k, Integrable (Fk k) P)
    (hBudget : ∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A → ∀ k,
      (∫ ω in A ∩ {η : Ω | σk k η ≠ 0}, Fk k ω ∂P) ≤
        w x * (P (A ∩ {η : Ω | σ η ≠ 0})).toReal) :
    ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P F ω ≤ w x := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hFpos := avram_ubv_loc6_original_any_clock_exact_closed_payoff_nonnegative X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad x hxc D hD q σ F hFsource
  have hFkpos : ∀ k ω, 0 ≤ Fk k ω := fun k =>
    avram_ubv_loc6_original_any_clock_exact_closed_payoff_nonnegative X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad x hxc D hD q (σk k) (Fk k) (hFksource k)
  have hPositive (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A) :
      (∫ ω in A ∩ {η : Ω | σ η ≠ 0}, F ω ∂P) ≤ w x * (P (A ∩ {η : Ω | σ η ≠ 0})).toReal := by
    exact avram_mix_fin19_original_spatial_reward_eventwise_fatou_from_exact_cofinal X x q w D n σ hσbound S hSmono hSsup σk hσk F Fk hFsource hFksource hσmeas hσkmeas hσkle hFI.aestronglyMeasurable hFkmeas hFkint (fun ω _ => hFpos ω) (fun k ω _ => hFkpos k ω) A ((𝓕.rightCont).le 0 A hA) (w x * (P (A ∩ {η : Ω | σ η ≠ 0})).toReal) (mul_nonneg hwx ENNReal.toReal_nonneg) (hBudget A hA)
  have hZ : MeasurableSet[𝓕.rightCont 0] {ω : Ω | σ ω = 0} := by
    have hpos := avram_ubv_finite12_positive_clock_initial_measurable σ hσstop
    have hcomp : MeasurableSet[𝓕.rightCont 0] ({ω : Ω | σ ω ≠ 0}ᶜ) := hpos.compl
    convert hcomp using 1
    ext ω
    simp
  have hZero : ∀ ω ∈ {ω : Ω | σ ω = 0}, F ω ≤ w x := by
    intro ω hω
    exact avram_ubv_loc6_original_zero_clock_exact_physical_F_le X x q w C D hD hjump (fun _ : ℕ => σ) (fun _ : ℕ => F) (by intro k η; exact hFsource η) 0 ω hω
  have hAll : ∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A → (∫ ω in A, F ω ∂P) ≤ w x * (P A).toReal :=
    avram_ubv_jump11_initial_event_positive_clock_partition (𝓕.rightCont 0) ((𝓕.rightCont).le 0) {ω : Ω | σ ω = 0} hZ F hFI (w x) hZero (by intro A hA; simpa only [Set.compl_setOf, not_not] using hPositive A hA)
  exact avram_ubv_finite14_initial_event_budget_to_condexp F (w x) hFI hAll
