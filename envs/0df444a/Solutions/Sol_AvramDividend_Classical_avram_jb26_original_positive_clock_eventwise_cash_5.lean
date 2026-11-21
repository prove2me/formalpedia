-- Prove2me | solution 5 for AvramDividend.Classical.avram_jb26_original_positive_clock_eventwise_cash
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:30:56.51499+00:00
-- url     : https://prove2.me/submissions/807298df-4c84-4110-8b91-315af9a873c6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jump6_E_original_finiteactivity_ruinclipped_stop_F0_bound
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin36_original_finitecap_any_stopped_full_reward_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_initial_mask_conditional_upper_implies_eventwise_integral_budget
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
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
∀ ω, ρ ω ≤ (n : ℝ≥0)) (hρclip : ∀ ω, ρ ω ≤ (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
(hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤) (hCfinite : C ≠ ⊤) (κ : ℕ → Ω → ℝ≥0) (hκexact : ∀ k ω, κ
k ω = (min (ρ ω : ℝ≥0∞) (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal) (hκstop : ∀ k,
IsStoppingTime 𝓕.rightCont (fun ω => (κ k ω : WithTop ℝ≥0))) (H : ℕ → Ω → ℝ) (hHsource : ∀ k ω, H
k ω = Real.exp (-(q * (κ k ω : ℝ))) * w (if κ k ω = 0 ∨ (κ k ω : ℝ≥0∞) < ruinTime X x D ω then x +
X.X (κ k ω) ω - rightLimit D (κ k ω) ω else riskProcess X x D (κ k ω) ω) + (∫⁻ s in paymentTimes
(ruinTime X x D ω) ∩ Iic (κ k ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D
ω)).toReal) : ∀ k (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A → (∫ ω in A ∩ {η : Ω | κ k η ≠ 0}, H
k ω ∂P) ≤ w x * (P (A ∩ {η : Ω | κ k η ≠ 0})).toReal := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k A hA
  have hκle : ∀ ω, κ k ω ≤ ρ ω := by
    intro ω
    have hmin := ENNReal.toNNReal_mono
      (show (ρ ω : ℝ≥0∞) ≠ ⊤ by simp)
      (min_le_left (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((k : ℝ) + 1) ω))
    rw [hκexact k ω]
    simpa using hmin
  have hκbound : ∀ ω, κ k ω ≤ (n : ℝ≥0) := by
    intro ω
    exact (hκle ω).trans (hρbound ω)
  have hκclip : ∀ ω, κ k ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal := by
    intro ω
    exact (hκle ω).trans (hρclip ω)
  have hHI : Integrable (H k) P :=
    avram_mix_fin36_original_finitecap_any_stopped_full_reward_L1
      X x q (le_of_lt hq) w hw_cont hw_neg C hCfinite hxc D hD
      n (κ k) (hκstop k) hκbound (H k) (hHsource k)
  have hCE : ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont 0) P (H k) ω ≤ w x :=
    avram_jump6_E_original_finiteactivity_ruinclipped_stop_F0_bound
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn
      (κ k) (hκstop k) hκbound hκclip (H k) (hHsource k)
      hHI hFiniteActivity
  have hE : MeasurableSet[𝓕.rightCont 0]
      (A ∩ {ω : Ω | κ k ω ≠ 0}) :=
    hA.inter (avram_ubv_finite12_positive_clock_initial_measurable
      (κ k) (hκstop k))
  exact avram_jump6_A_initial_mask_conditional_upper_implies_eventwise_integral_budget
    (𝓕.rightCont 0) (𝓕.rightCont.le 0)
    (A ∩ {ω : Ω | κ k ω ≠ 0}) hE (H k) hHI (w x) hCE
