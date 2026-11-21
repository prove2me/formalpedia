-- Prove2me | solution 4 for AvramDividend.Classical.avram_mix_fin28_original_one_clock_positive_event_cash_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:15:16.657671+00:00
-- url     : https://prove2.me/submissions/4d513f9a-8ec8-431d-9105-c7f6cd9a2f78
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin36_original_finitecap_any_stopped_full_reward_L1
import Theorems.Thm_AvramDividend_Classical_avram_jump6_E_original_finiteactivity_ruinclipped_stop_F0_bound
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_initial_mask_conditional_upper_implies_eventwise_integral_budget
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X :
SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ :
X.σ ≠ 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw0 : 0 ≤ w 0) (hw_cont :
ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧
ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y
∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
(x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
(hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω))
(hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w
(riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0
< n) (ρ : Ω → ℝ≥0) (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) (hρbound :
∀ ω, ρ ω ≤ (n : ℝ≥0)) (hρclip : ∀ ω, ρ ω ≤ (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (G : Ω →
ℝ) (hGsource : ∀ ω, G ω = Real.exp (-(q * (ρ ω : ℝ))) * w (if ρ ω = 0 ∨ (ρ ω : ℝ≥0∞) < ruinTime X
x D ω then x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω else riskProcess X x D (ρ ω) ω) + (∫⁻ s in
paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s)))
∂(dividendMeasure D ω)).toReal) (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤) (hCfinite : C ≠ ⊤) : ∀ A
: Set Ω, MeasurableSet[𝓕.rightCont 0] A → (∫ ω in A ∩ {ω : Ω | ρ ω ≠ 0}, G ω ∂P) ≤ w x * (P (A ∩
{ω : Ω | ρ ω ≠ 0})).toReal := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hGI : Integrable G P :=
    avram_mix_fin36_original_finitecap_any_stopped_full_reward_L1
      X x q (le_of_lt hq) w hw_cont hw_neg C hCfinite hxc D hD
      n ρ hρstop hρbound G hGsource
  have hUpper : ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont 0) P G ω ≤ w x :=
    avram_jump6_E_original_finiteactivity_ruinclipped_stop_F0_bound
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn
      ρ hρstop hρbound hρclip G hGsource hGI hFiniteActivity
  intro A hA
  have hEv : MeasurableSet[𝓕.rightCont 0]
      (A ∩ {ω : Ω | ρ ω ≠ 0}) :=
    hA.inter (avram_ubv_finite12_positive_clock_initial_measurable ρ hρstop)
  exact avram_jump6_A_initial_mask_conditional_upper_implies_eventwise_integral_budget
    (𝓕.rightCont 0) (𝓕.rightCont.le 0)
    (A ∩ {ω : Ω | ρ ω ≠ 0}) hEv G hGI (w x) hUpper
