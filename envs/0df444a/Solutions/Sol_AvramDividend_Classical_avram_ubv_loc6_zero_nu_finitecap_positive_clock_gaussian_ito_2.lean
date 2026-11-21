-- Prove2me | solution 2 for AvramDividend.Classical.avram_ubv_loc6_zero_nu_finitecap_positive_clock_gaussian_ito
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T11:44:32.510275+00:00
-- url     : https://prove2.me/submissions/bbe6d6d6-8d07-4ad8-a6d8-592ddefc0b48
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian11_finitecap_conditional_source_expected_budget
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_event_expected_budget_supports_centered_ae
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

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
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P) :
    ∀ k, ∃ Mc G R : Ω → ℝ,
      Integrable Mc P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∀ ω, σ k ω = 0 → Mc ω = 0) ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧ (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P, σ k ω ≠ 0 →
        F k ω ≤ w x + Mc ω + G ω + R ω) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k
  let A : Set Ω := {ω : Ω | σ k ω ≠ 0}
  have hSource :=
    avram_ubv_gaussian11_finitecap_conditional_source_expected_budget
      X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm
      hTermMeas hCashI σ F hσstop hσle hFsource hFI k
  obtain ⟨hA, hBudget⟩ := hSource
  obtain ⟨M, hMI, hMmean, hMzeroAE, hBoundAE⟩ :=
    avram_jump6_B_event_expected_budget_supports_centered_ae
      A hA (F k) (hFI k) (w x) hBudget
  let Mc : Ω → ℝ := fun ω => if ω ∈ A then M ω else 0
  have hMcEq : Mc =ᵐ[P] M := by
    filter_upwards [hMzeroAE] with ω hω
    by_cases hωA : ω ∈ A
    · simp [Mc, hωA]
    · simp [Mc, hωA, hω hωA]
  have hMcI : Integrable Mc P := hMI.congr hMcEq.symm
  have hMcmean : (∫ ω, Mc ω ∂P) = 0 := by
    rw [integral_congr_ae hMcEq]
    exact hMmean
  refine ⟨Mc, (fun _ => (0 : ℝ)), (fun _ => (0 : ℝ)),
    hMcI, hMcmean, ?_, ?_, ?_, ?_⟩
  · intro ω hω
    simp [Mc, A, hω]
  · filter_upwards [] with ω
    norm_num
  · filter_upwards [] with ω
    norm_num
  · filter_upwards [hBoundAE] with ω hω
    intro hpos
    have hωA : ω ∈ A := hpos
    simpa [Mc, hωA] using hω hωA
