-- Prove2me | solution 4 for AvramDividend.Classical.avram_jb19_original_spatial_two_noise_ledger
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:32:51.600375+00:00
-- url     : https://prove2.me/submissions/409558ff-26a4-4505-abcd-dfefac6b0872
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_conditional_upper_to_exact_centered_martingale_budget
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_true_clipped_finitecap_F0_discounted_reward_upper
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin36_original_finitecap_any_stopped_full_reward_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X :
    SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0)
    (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2
    w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
    X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y →
    ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D
    : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞)
    < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t :
    ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w
    (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) (hρbound : ∀ ω, ρ ω ≤
    (n : ℝ≥0)) (hρclip : ∀ ω, ρ ω ≤ (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤) (hCfinite : C ≠ ⊤) (κ : ℕ → Ω → ℝ≥0) (hκexact : ∀
    k ω, κ k ω = (min (ρ ω : ℝ≥0∞) (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal) (hκstop :
    ∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (κ k ω : WithTop ℝ≥0))) (H : ℕ → Ω → ℝ) (hHsource
    : ∀ k ω, H k ω = Real.exp (-(q * (κ k ω : ℝ))) * w (if κ k ω = 0 ∨ (κ k ω : ℝ≥0∞) <
    ruinTime X x D ω then x + X.X (κ k ω) ω - rightLimit D (κ k ω) ω else riskProcess X x D (κ
    k ω) ω) + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ k ω : ℝ), ENNReal.ofReal
    (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) : ∀ (A : Set Ω),
    MeasurableSet[𝓕.rightCont 0] A → ∀ k, Integrable (H k) P ∧ ∃ MG MJ B : Ω → ℝ, Integrable MG
    P ∧ Integrable MJ P ∧ P[MG | 𝓕.rightCont 0] =ᵐ[P] 0 ∧ P[MJ | 𝓕.rightCont 0] =ᵐ[P] 0 ∧ (∀ᵐ ω
    ∂(P.restrict (A ∩ {η : Ω | κ k η ≠ 0})), B ω ≤ 0) ∧ (∀ᵐ ω ∂(P.restrict (A ∩ {η : Ω | κ k η
    ≠ 0})), H k ω ≤ w x + MG ω + MJ ω + B ω) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro A hA k
  have hκle : ∀ ω, κ k ω ≤ ρ ω := by
    intro ω
    rw [hκexact k ω]
    have hmin :
        (min (ρ ω : ℝ≥0∞) (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal
          ≤ (ρ ω : ℝ≥0∞).toNNReal :=
      ENNReal.toNNReal_mono (by simp)
        (min_le_left _ _)
    simpa only [ENNReal.toNNReal_coe] using hmin
  have hκbound : ∀ ω, κ k ω ≤ (n : ℝ≥0) :=
    fun ω => (hκle ω).trans (hρbound ω)
  have hκclip : ∀ ω, κ k ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal :=
    fun ω => (hκle ω).trans (hρclip ω)
  have hHI : Integrable (H k) P :=
    avram_mix_fin36_original_finitecap_any_stopped_full_reward_L1
      X x q (le_of_lt hq) w hw_cont hw_neg C hCfinite hxc
      D hD n (κ k) (hκstop k) hκbound (H k) (hHsource k)
  have hUpper : ∀ᵐ ω ∂P,
      P[H k | 𝓕.rightCont 0] ω ≤ w x :=
    (avram_jump6_A_true_clipped_finitecap_F0_discounted_reward_upper
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn ρ hρstop hρbound hρclip hFiniteActivity hCfinite
      κ hκexact hκstop H hHsource k).2
  obtain ⟨MG, MJ, B, hMGI, hMJI, hMG0, hMJ0, hBS, hEq⟩ :=
    avram_jump6_A_conditional_upper_to_exact_centered_martingale_budget
      (𝓕.rightCont 0) (𝓕.rightCont.le 0) (H k) hHI (w x) hUpper
  refine ⟨hHI, MG, MJ, B, hMGI, hMJI, hMG0, hMJ0, ?_, ?_⟩
  · exact ae_restrict_of_ae hBS
  · apply Filter.Eventually.of_forall
    intro ω
    exact (hEq ω).le
