-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite33_original_preexit_stopped_ito_martingale_envelope
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T10:22:10.000985+00:00
-- url     : https://prove2.me/submissions/5331e5aa-b36d-4bac-973f-48276dd9833d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gfinite34_original_preexit_masked_reward_condexp_upper
import Theorems.Thm_AvramDividend_Classical_avram_gfinite28_original_bounded_stop_masked_strict_reward_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_condexp_upper_to_centred_witness
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds

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
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
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
    (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k (ρ : Ω → ℝ≥0)
      (hρstop : IsStoppingTime 𝓕.rightCont
        (fun ω => (ρ ω : WithTop ℝ≥0)))
      (hρle : ∀ ω, ρ ω ≤ σ k ω)
      (δ : ℝ) (hδ : 0 < δ)
      (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
        δ ≤ riskProcess X x D t ω)
      (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      ∃ M : Ω → ℝ,
        IntegrableOn M (A ∩ {η : Ω | ρ η ≠ 0}) P ∧
        (∫ ω in A ∩ {η : Ω | ρ η ≠ 0}, M ω ∂P) = 0 ∧
        (∀ᵐ ω ∂(P.restrict (A ∩ {η : Ω | ρ η ≠ 0})),
          (Real.exp (-(q * (ρ ω : ℝ))) *
              w (riskProcess X x D (ρ ω) ω) +
            (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
              ENNReal.ofReal (Real.exp (-(q * s)))
              ∂(dividendMeasure D ω)).toReal) ≤ w x + M ω) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k ρ hρstop hρle δ hδ hFloor A hA
  let E : Set Ω := A ∩ {η : Ω | ρ η ≠ 0}
  let F : Ω → ℝ := fun η =>
    if ρ η = 0 then w x else
      Real.exp (-(q * (ρ η : ℝ))) *
        w (riskProcess X x D (ρ η) η) +
      (∫⁻ s in paymentTimes (ruinTime X x D η) ∩ Iio (ρ η : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D η)).toReal
  have hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0) := by
    intro ω
    calc
      ρ ω ≤ σ k ω := hρle ω
      _ ≤ τ ω := hσle k ω
      _ ≤ (n : ℝ≥0) := by
        rw [hτeq ω]
        exact (avram_wave7_08_source_truncated_clock_nnreal_bounds X x D n).2.1 ω
  have hFI : Integrable F P := by
    exact avram_gfinite28_original_bounded_stop_masked_strict_reward_L1
      X x C hFiniteCap hxc D hD w hw_cont hw_neg q hq
      ρ hρstop (n : ℝ≥0) hρbound
  have hCond : ∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P F ω ≤ w x :=
    avram_gfinite34_original_preexit_masked_reward_condexp_upper
      X hX hBV hν q hq w C hC hFiniteCap
      hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop σ hσstop hσle
      k ρ hρstop hρle δ hδ hFloor
  obtain ⟨M, hMI, hCondM, hUpper⟩ :=
    avram_ubv_finite12_condexp_upper_to_centred_witness
      (𝓕 := 𝓕) (w x) F hFI hCond
  have hρzero : MeasurableSet[𝓕.rightCont 0] {η : Ω | ρ η = 0} := by
    simpa only [WithTop.coe_le_coe, nonpos_iff_eq_zero] using
      (hρstop (0 : ℝ≥0))
  have hE : MeasurableSet[𝓕.rightCont 0] E := by
    dsimp [E]
    exact hA.inter (by simpa only [Set.compl_setOf] using hρzero.compl)
  have hm : 𝓕.rightCont 0 ≤ mΩ := (𝓕.rightCont).le 0
  have hMean0 : (∫ ω in E, M ω ∂P) = 0 := by
    calc
      (∫ ω in E, M ω ∂P) =
          ∫ ω in E, condExp (𝓕.rightCont 0) P M ω ∂P :=
        (setIntegral_condExp hm hMI hE).symm
      _ = ∫ ω in E, (0 : ℝ) ∂P := by
        exact integral_congr_ae (ae_restrict_of_ae hCondM)
      _ = 0 := by simp
  have hUpperE : ∀ᵐ ω ∂(P.restrict E),
      (Real.exp (-(q * (ρ ω : ℝ))) *
          w (riskProcess X x D (ρ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) ≤ w x + M ω := by
    filter_upwards [ae_restrict_mem (hm E hE), ae_restrict_of_ae hUpper] with ω hωE hωUpper
    have hρnz : ρ ω ≠ 0 := hωE.2
    simpa only [F, if_neg hρnz] using hωUpper
  refine ⟨M, hMI.integrableOn, ?_, ?_⟩
  · simpa only [E] using hMean0
  · simpa only [E] using hUpperE
