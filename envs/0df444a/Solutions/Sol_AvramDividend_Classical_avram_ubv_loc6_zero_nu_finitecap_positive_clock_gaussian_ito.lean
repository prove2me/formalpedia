-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_loc6_zero_nu_finitecap_positive_clock_gaussian_ito
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:51:04.328632+00:00
-- url     : https://prove2.me/submissions/dad71f66-6cba-4af4-9b4c-bd875f168ebc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian11_conditional_budget_zero_clock_centering
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian11_finitecap_conditional_source_expected_budget

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
  obtain ⟨hAmeas, hBudget⟩ :=
    avram_ubv_gaussian11_finitecap_conditional_source_expected_budget
      X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm
      hTermMeas hCashI σ F hσstop hσle hFsource hFI k
  let A : Set Ω := {ω | σ k ω ≠ 0}
  change MeasurableSet A at hAmeas
  change (∫ ω in A, F k ω ∂P) ≤ w x * (P A).toReal at hBudget
  by_cases hApos : 0 < (P A).toReal
  · obtain ⟨M, hMI, hMzero, hMoff, hMupper⟩ :=
      avram_ubv_gaussian11_conditional_budget_zero_clock_centering
        A hAmeas hApos (F k) (hFI k) (w x) hBudget
    refine ⟨M, (fun _ => 0), (fun _ => 0),
      hMI, hMzero, ?_, ?_, ?_, ?_⟩
    · intro ω hσ
      apply hMoff ω
      simpa [A] using hσ
    · filter_upwards [] with ω
      simp
    · filter_upwards [] with ω
      simp
    · filter_upwards [] with ω
      intro hσ
      have hω : ω ∈ A := hσ
      simpa using hMupper ω hω
  · have hA0 : (P A).toReal = 0 :=
      le_antisymm (le_of_not_gt hApos) ENNReal.toReal_nonneg
    have hPfinite : P A ≠ ⊤ := measure_ne_top P A
    have hPzero : P A = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff (P A)).mp hA0 with hz | ht
      · exact hz
      · exact (hPfinite ht).elim
    have hAlmostOff : ∀ᵐ ω ∂P, ω ∉ A := by
      apply (ae_iff).2
      simpa only [not_not, setOf_mem_eq] using hPzero
    refine ⟨(fun _ => 0), (fun _ => 0), (fun _ => 0),
      integrable_const 0, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · intro ω hσ
      rfl
    · filter_upwards [] with ω
      simp
    · filter_upwards [] with ω
      simp
    · filter_upwards [hAlmostOff] with ω hOff
      intro hσ
      exact (hOff (by simpa [A] using hσ)).elim
