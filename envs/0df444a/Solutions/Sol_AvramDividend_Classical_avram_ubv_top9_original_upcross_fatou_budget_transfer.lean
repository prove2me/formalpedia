-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top9_original_upcross_fatou_budget_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:13:24.202316+00:00
-- url     : https://prove2.me/submissions/8450ad03-f066-4079-917b-d5cc203b1c14

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_any_clock_source_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_infinitecap_candidate_globally_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_any_clock_exact_closed_payoff_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_ae_natural_clock_fatou_L1_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Source exact nonnegative Fatou transfer, with no martingale UI hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hCtop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (ρ ω : ℝ))) *
        w (if ρ ω = 0 ∨ (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
          else riskProcess X x D (ρ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (κ : ℕ → Ω → ℝ≥0)
    (hκstop : ∀ j, IsStoppingTime 𝓕.rightCont
      (fun ω => (κ j ω : WithTop ℝ≥0)))
    (H : ℕ → Ω → ℝ)
    (hHsource : ∀ j ω, H j ω =
      Real.exp (-(q * (κ j ω : ℝ))) *
        w (if κ j ω = 0 ∨ (κ j ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (κ j ω) ω - rightLimit D (κ j ω) ω
          else riskProcess X x D (κ j ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ j ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hHI : ∀ j, Integrable (H j) P)
    (hEventually : ∀ ω, ∀ᶠ j : ℕ in atTop, κ j ω = ρ ω)
    (hBudget : ∀ j, (∫ ω, H j ω ∂P) ≤ w x) :
    (∫ ω, F ω ∂P) ≤ w x := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hwx : 0 ≤ w x := avram_ubv_loc6_infinitecap_candidate_globally_nonnegative
    C hC w hw0 hw_cont hw_neg hw_smooth hw_grad hCtop x
  have hFm : Measurable F :=
    avram_ubv_top9_original_any_clock_source_reward_measurable
      X x q w hw_cont hw_neg D hD.1.1 ρ hρstop F hFsource
  have hHm : ∀ j, Measurable (H j) := fun j =>
    avram_ubv_top9_original_any_clock_source_reward_measurable
      X x q w hw_cont hw_neg D hD.1.1 (κ j) (hκstop j) (H j) (hHsource j)
  have hFnn : ∀ ω, 0 ≤ F ω :=
    avram_ubv_loc6_original_any_clock_exact_closed_payoff_nonnegative
      X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hxc D hD q ρ F hFsource
  have hHnn : ∀ j, 0 ≤ᵐ[P] H j := fun j => Filter.Eventually.of_forall
    (avram_ubv_loc6_original_any_clock_exact_closed_payoff_nonnegative
        X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
        x hxc D hD q (κ j) (H j) (hHsource j))
  have hlim : ∀ᵐ ω ∂P, Tendsto
      (fun j => ENNReal.ofReal (H j ω)) atTop
      (𝓝 (ENNReal.ofReal (F ω))) := by
    filter_upwards [] with ω
    have he : (fun j => ENNReal.ofReal (H j ω)) =ᶠ[atTop]
        (fun _ => ENNReal.ofReal (F ω)) := by
      filter_upwards [hEventually ω] with j hj
      have hR : H j ω = F ω := by rw [hHsource j ω, hj]; exact (hFsource ω).symm
      exact congrArg ENNReal.ofReal hR
    exact (tendsto_congr' he).2 tendsto_const_nhds
  exact (avram_p4_f4_ae_natural_clock_fatou_L1_budget
    P F H hFm.aestronglyMeasurable
    (Filter.Eventually.of_forall hFnn) hHm hHI hHnn
    hlim (w x) hwx hBudget).2
