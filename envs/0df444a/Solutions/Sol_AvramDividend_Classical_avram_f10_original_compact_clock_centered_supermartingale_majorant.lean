-- Prove2me | solution 1 for AvramDividend.Classical.avram_f10_original_compact_clock_centered_supermartingale_majorant
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:13:28.099718+00:00
-- url     : https://prove2.me/submissions/3f5906e8-4cbd-4037-aefc-adf5f3bc7caf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f8_zero_nu_original_exact_clock_HJB_expected_upper
import Theorems.Thm_AvramDividend_Classical_avram_p4_f8_nonzero_nu_original_exact_clock_HJB_expected_upper

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Extract one centred L1 majorant from the source-exact Gaussian or
    compensated-jump original stopped HJB expectation inequality. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
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
    (hFformula : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFmeas : ∀ k, Measurable (F k))
    (hFI : ∀ k, Integrable (F k) P)
    (hFpos : ∀ k, 0 ≤ᵐ[P] F k) :
    ∀ k : ℕ, ∃ M : Ω → ℝ,
      Integrable M P ∧ (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, F k ω ≤ w x + M ω) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hBudget : ∀ k, (∫ ω, F k ω ∂P) ≤ w x := by
    by_cases hν : X.ν = 0
    · exact avram_p4_f8_zero_nu_original_exact_clock_HJB_expected_upper
        X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth
        hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn
        τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm
        hTermMeas hCashI σ F hσstop hσle hFformula hFI hν
    · exact avram_p4_f8_nonzero_nu_original_exact_clock_HJB_expected_upper
        X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth
        hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn
        τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm
        hTermMeas hCashI σ F hσstop hσle hFformula hFI hν
  intro k
  let M : Ω → ℝ := fun ω => F k ω - (∫ ξ, F k ξ ∂P)
  have hMI : Integrable M P := (hFI k).sub (integrable_const _)
  have hMzero : (∫ ω, M ω ∂P) = 0 := by
    dsimp [M]
    rw [integral_sub (hFI k) (integrable_const _)]
    simp
  have hUpper : ∀ᵐ ω ∂P, F k ω ≤ w x + M ω := by
    filter_upwards [] with ω
    dsimp [M]
    linarith [hBudget k]
  exact ⟨M, hMI, hMzero, hUpper⟩
