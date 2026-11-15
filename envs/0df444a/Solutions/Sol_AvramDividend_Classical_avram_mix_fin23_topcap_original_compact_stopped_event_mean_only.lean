-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin23_topcap_original_compact_stopped_event_mean_only
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:20:23.474201+00:00
-- url     : https://prove2.me/submissions/b200461c-a36f-4f61-8c91-c692c2085df4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_avram_b215_original_finiteactivity_stopped_cash_initial_condexp_upper
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin22_topcap_compact_reward_L1_of_full_F
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin22_positive_initial_from_closed_cap_gradient
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0)
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
    (n : ℕ) (hn : 0 < n) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (hσclip : ∀ ω, σ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (F : Ω → ℝ) (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D ω then
          x + X.X (σ ω) ω - rightLimit D (σ ω) ω
        else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P) (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hCtop : C = ⊤) (κ : ℕ → Ω → ℝ≥0)
    (hκstop : ∀ j, IsStoppingTime 𝓕.rightCont
      (fun ω => (κ j ω : WithTop ℝ≥0)))
    (hκle : ∀ j ω, κ j ω ≤ σ ω) (hκbound : ∀ j ω, X.X (κ j ω) ω ≤ (j : ℝ) + 1)
    (H : ℕ → Ω → ℝ)
    (hHsource : ∀ j ω, H j ω =
      Real.exp (-(q * (κ j ω : ℝ))) *
        w (if κ j ω = 0 ∨ (κ j ω : ℝ≥0∞) < ruinTime X x D ω then
          x + X.X (κ j ω) ω - rightLimit D (κ j ω) ω
        else riskProcess X x D (κ j ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (κ j ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) :
    ∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
      ∀ j, (∫ ω in A ∩ {η : Ω | κ j η ≠ 0}, H j ω ∂P) ≤
        w x * (P (A ∩ {η : Ω | σ η ≠ 0})).toReal := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hwpos : 0 ≤ w x := avram_mix_fin22_positive_initial_from_closed_cap_gradient
      C hC w hw0 hw_cont hw_smooth hw_grad x hx hxc
  have hHI : ∀ j, Integrable (H j) P := by
    intro j; exact (avram_mix_fin22_topcap_compact_reward_L1_of_full_F
      X hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hxc D hD σ hσstop F hFsource hFI
      κ hκstop hκle hκbound H hHsource j).1
  intro A hA j
  have hkBound : ∀ ω, κ j ω ≤ (n : ℝ≥0) := fun ω =>
    (hκle j ω).trans (hσbound ω)
  have hCond : ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P (H j) ω ≤ w x :=
    avram_b215_original_finiteactivity_stopped_cash_initial_condexp_upper
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn (κ j) (hκstop j) hkBound (H j)
      (hHsource j) (hHI j) hFiniteActivity
  have hκPositive : MeasurableSet[𝓕.rightCont 0] {ω : Ω | κ j ω ≠ 0} :=
    avram_ubv_finite12_positive_clock_initial_measurable
      (κ j) (hκstop j)
  let E : Set Ω := A ∩ {ω : Ω | κ j ω ≠ 0}
  have hE : MeasurableSet[𝓕.rightCont 0] E := hA.inter hκPositive
  have hSetCond : (∫ ω in E, condExp (𝓕.rightCont 0) P (H j) ω ∂P) =
        ∫ ω in E, H j ω ∂P :=
    setIntegral_condExp ((𝓕.rightCont).le 0) (hHI j) hE
  have hMono : (∫ ω in E, condExp (𝓕.rightCont 0) P (H j) ω ∂P) ≤
        ∫ ω in E, (w x : ℝ) ∂P := by
    exact integral_mono_ae (integrable_condExp.integrableOn)
      (integrable_const (w x)) (ae_restrict_of_ae hCond)
  have hSubset : E ⊆ A ∩ {ω : Ω | σ ω ≠ 0} := by
    intro ω hω
    refine ⟨hω.1, ?_⟩
    intro hzero
    have hkZero : κ j ω ≤ 0 := by simpa only [hzero] using hκle j ω
    exact hω.2 (le_antisymm hkZero zero_le)
  calc
    (∫ ω in A ∩ {η : Ω | κ j η ≠ 0}, H j ω ∂P) =
        ∫ ω in E, H j ω ∂P := rfl
    _ = ∫ ω in E, condExp (𝓕.rightCont 0) P (H j) ω ∂P := hSetCond.symm
    _ ≤ ∫ ω in E, (w x : ℝ) ∂P := hMono
    _ = w x * (P E).toReal := by
      simp [setIntegral_const, smul_eq_mul, mul_comm]
      left; rfl
    _ ≤ w x * (P (A ∩ {η : Ω | σ η ≠ 0})).toReal := by
      exact mul_le_mul_of_nonneg_left (measureReal_mono hSubset) hwpos
