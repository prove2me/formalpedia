-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin28_original_one_clock_positive_event_cash_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T00:31:54.901999+00:00
-- url     : https://prove2.me/submissions/e2c503b6-ea74-4007-a563-394152085ebc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin20_original_true_spatial_clocks_with_cofinality
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin20_original_true_local_rewards_meas_integrable
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin35_original_true_spatial_stopped_ito_event_budget
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin19_original_spatial_reward_eventwise_fatou_from_exact_cofinal
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_any_clock_exact_closed_payoff_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin36_original_finitecap_any_stopped_full_reward_L1
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin22_positive_initial_from_closed_cap_gradient
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
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
    (n : ℕ) (hn : 0 < n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (hρclip : ∀ ω, ρ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (G : Ω → ℝ)
    (hGsource : ∀ ω, G ω =
      Real.exp (-(q * (ρ ω : ℝ))) *
        w (if ρ ω = 0 ∨
              (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
          else riskProcess X x D (ρ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hCfinite : C ≠ ⊤) :
    ∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A ∩ {ω : Ω | ρ ω ≠ 0}, G ω ∂P) ≤
        w x * (P (A ∩ {ω : Ω | ρ ω ≠ 0})).toReal := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hGI :=
    avram_mix_fin36_original_finitecap_any_stopped_full_reward_L1
      X x q (le_of_lt hq) w hw_cont hw_neg C hCfinite
      hxc D hD n ρ hρstop hρbound G hGsource
  obtain ⟨S, ρk, hSsource, hSmono, hSsup, hρkeq,
      hρkstop, hρkle, _⟩ :=
    avram_mix_fin20_original_true_spatial_clocks_with_cofinality
      X (n : ℝ≥0) ρ hρstop hρbound
  let Gk : ℕ → Ω → ℝ := fun k ω =>
    Real.exp (-(q * (ρk k ω : ℝ))) *
      w (if ρk k ω = 0 ∨
            (ρk k ω : ℝ≥0∞) < ruinTime X x D ω then
          x + X.X (ρk k ω) ω - rightLimit D (ρk k ω) ω
        else riskProcess X x D (ρk k ω) ω) +
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρk k ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)).toReal
  have hGksource : ∀ k ω, Gk k ω =
      Real.exp (-(q * (ρk k ω : ℝ))) *
        w (if ρk k ω = 0 ∨
              (ρk k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (ρk k ω) ω - rightLimit D (ρk k ω) ω
          else riskProcess X x D (ρk k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρk k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal := by
    intro k ω
    rfl
  have hLocal :=
    avram_mix_fin20_original_true_local_rewards_meas_integrable
      X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hxc D hD hD.1.1 q (le_of_lt hq) ρ hρstop G
      hGsource hGI hCfinite ρk hρkstop hρkle Gk hGksource
  have hκexact : ∀ k ω, ρk k ω =
      (min (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal := by
    intro k ω
    rw [hρkeq k ω, hSsource k ω]
  have hBudget :=
    avram_mix_fin35_original_true_spatial_stopped_ito_event_budget
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn
      ρ hρstop hρbound hρclip hFiniteActivity hCfinite
      ρk hκexact hρkstop Gk hGksource
  have hGpos :=
    avram_ubv_loc6_original_any_clock_exact_closed_payoff_nonnegative
      X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hxc D hD q ρ G hGsource
  have hGkpos : ∀ k ω, 0 ≤ Gk k ω := by
    intro k ω
    exact avram_ubv_loc6_original_any_clock_exact_closed_payoff_nonnegative
      X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hxc D hD q (ρk k) (Gk k) (hGksource k) ω
  have hwx : 0 ≤ w x :=
    avram_mix_fin22_positive_initial_from_closed_cap_gradient
      C hC w hw0 hw_cont hw_smooth hw_grad x hx hxc
  have hρmeas : Measurable ρ :=
    measurable_coe_nnreal_ennreal_iff.mp hρstop.measurable'
  have hρkmeas : ∀ k, Measurable (ρk k) := by
    intro k
    exact measurable_coe_nnreal_ennreal_iff.mp (hρkstop k).measurable'
  have hρboundENN : ∀ ω, (ρ ω : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
    intro ω
    exact ENNReal.coe_le_coe.mpr (hρbound ω)
  intro A hA
  have hAglobal : MeasurableSet A :=
    (𝓕.rightCont).le 0 A hA
  have hFatou :=
    avram_mix_fin19_original_spatial_reward_eventwise_fatou_from_exact_cofinal
      X x q w D n ρ hρboundENN S hSmono
      (Filter.Eventually.of_forall hSsup)
      ρk hρkeq G Gk hGsource hGksource
      hρmeas hρkmeas hρkle hGI.aestronglyMeasurable
      hLocal.1 hLocal.2 (fun ω _ => hGpos ω)
      (fun k ω _ => hGkpos k ω) A hAglobal
      (w x * (P (A ∩ {ω : Ω | ρ ω ≠ 0})).toReal)
      (mul_nonneg hwx ENNReal.toReal_nonneg) (hBudget A hA)
  exact hFatou
