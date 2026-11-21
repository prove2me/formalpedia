-- Prove2me | solution 2 for AvramDividend.Classical.avram_mix_fin21_original_bounded_stop_event_ito_cash_upper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:19:35.527087+00:00
-- url     : https://prove2.me/submissions/16b2247e-e608-4610-8b99-3ba8df3bcd93
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jump6_E_original_finiteactivity_ruinclipped_stop_F0_bound
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin36_original_finitecap_any_stopped_full_reward_L1
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin22_positive_initial_from_closed_cap_gradient
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_initial_mask_conditional_upper_implies_eventwise_integral_budget
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin28_original_positive_clock_event_measure_mono
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
< n) (σ : Ω → ℝ≥0) (hσstop : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0))) (hσbound :
∀ ω, σ ω ≤ (n : ℝ≥0)) (hσclip : ∀ ω, σ ω ≤ (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (F : Ω →
ℝ) (hFsource : ∀ ω, F ω = Real.exp (-(q * (σ ω : ℝ))) * w (if σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X
x D ω then x + X.X (σ ω) ω - rightLimit D (σ ω) ω else riskProcess X x D (σ ω) ω) + (∫⁻ s in
paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s)))
∂(dividendMeasure D ω)).toReal) (hFI : Integrable F P) (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
(hCfinite : C ≠ ⊤) (σk : ℕ → Ω → ℝ≥0) (hσkle : ∀ k ω, σk k ω ≤ σ ω) (hσkstop : ∀ k, IsStoppingTime
𝓕.rightCont (fun ω => (σk k ω : WithTop ℝ≥0))) (Fk : ℕ → Ω → ℝ) (hFksource : ∀ k ω, Fk k ω =
Real.exp (-(q * (σk k ω : ℝ))) * w (if σk k ω = 0 ∨ (σk k ω : ℝ≥0∞) < ruinTime X x D ω then x +
X.X (σk k ω) ω - rightLimit D (σk k ω) ω else riskProcess X x D (σk k ω) ω) + (∫⁻ s in
paymentTimes (ruinTime X x D ω) ∩ Iic (σk k ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s)))
∂(dividendMeasure D ω)).toReal) : 0 ≤ w x ∧ ∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A → ∀ k : ℕ,
(∫ ω in A ∩ {ω : Ω | σk k ω ≠ 0}, Fk k ω ∂P) ≤ w x * (P (A ∩ {ω : Ω | σ ω ≠ 0})).toReal := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hwx : 0 ≤ w x :=
    avram_mix_fin22_positive_initial_from_closed_cap_gradient
      C hC w hw0 hw_cont hw_smooth hw_grad x hx hxc
  refine ⟨hwx, ?_⟩
  intro A hA k
  have hBound : ∀ ω, σk k ω ≤ (n : ℝ≥0) := by
    intro ω
    exact (hσkle k ω).trans (hσbound ω)
  have hClip : ∀ ω, σk k ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal := by
    intro ω
    exact (hσkle k ω).trans (hσclip ω)
  have hFI' : Integrable (Fk k) P :=
    avram_mix_fin36_original_finitecap_any_stopped_full_reward_L1
      X x q (le_of_lt hq) w hw_cont hw_neg C hCfinite hxc D hD
      n (σk k) (hσkstop k) hBound (Fk k) (hFksource k)
  have hCE : ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont 0) P (Fk k) ω ≤ w x :=
    avram_jump6_E_original_finiteactivity_ruinclipped_stop_F0_bound
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn
      (σk k) (hσkstop k) hBound hClip (Fk k) (hFksource k)
      hFI' hFiniteActivity
  have hE : MeasurableSet[𝓕.rightCont 0]
      (A ∩ {ω : Ω | σk k ω ≠ 0}) :=
    hA.inter (avram_ubv_finite12_positive_clock_initial_measurable
      (σk k) (hσkstop k))
  have hBudget :
      (∫ ω in A ∩ {ω : Ω | σk k ω ≠ 0}, Fk k ω ∂P) ≤
      w x * (P (A ∩ {ω : Ω | σk k ω ≠ 0})).toReal :=
    avram_jump6_A_initial_mask_conditional_upper_implies_eventwise_integral_budget
      (𝓕.rightCont 0) (𝓕.rightCont.le 0)
      (A ∩ {ω : Ω | σk k ω ≠ 0}) hE (Fk k) hFI' (w x) hCE
  have hMono :=
    avram_mix_fin28_original_positive_clock_event_measure_mono
      X σ (σk k) (hσkle k) A
  have hReal :
      (P (A ∩ {ω : Ω | σk k ω ≠ 0})).toReal ≤
      (P (A ∩ {ω : Ω | σ ω ≠ 0})).toReal :=
    ENNReal.toReal_mono (measure_lt_top P _).ne hMono
  exact hBudget.trans (mul_le_mul_of_nonneg_left hReal hwx)
