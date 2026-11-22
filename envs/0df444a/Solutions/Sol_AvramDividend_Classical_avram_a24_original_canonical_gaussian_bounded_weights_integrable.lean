-- Prove2me | solution 1 for AvramDividend.Classical.avram_a24_original_canonical_gaussian_bounded_weights_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:48:17.453796+00:00
-- url     : https://prove2.me/submissions/c955745d-b4b5-45d6-9bd5-1f6a637e72ab

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_canonical_clipped_gaussian_grid_conditional_first_second_moments
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Bounded predictable physical Gaussian weights have integrable cell gains. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (n : ℕ) (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (G H : ℕ → ℕ → Ω → ℝ)
    (hGmeas : ∀ j i, AEStronglyMeasurable (G j i) P)
    (hHmeas : ∀ j i, AEStronglyMeasurable (H j i) P)
    (BG BH : ℕ → ℕ → ℝ)
    (hGB : ∀ j i, ∀ᵐ ω ∂P, ‖G j i ω‖ ≤ BG j i)
    (hHB : ∀ j i, ∀ᵐ ω ∂P, ‖H j i ω‖ ≤ BH j i) :
    ∀ j i : ℕ,
      let δ : ℝ≥0 := (n : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)
      let τg : Ω → ℝ≥0 := fun ω => min ((i : ℝ≥0) * δ) (σ ω)
      let M : Ω → ℝ := fun ω =>
        X.X (τg ω + δ) ω - X.X (τg ω) ω - (δ : ℝ) * X.c
      Integrable (fun ω => G j i ω * M ω) P ∧
      Integrable (H j i) P ∧
      Integrable (fun ω => H j i ω * (M ω)^2) P:= by
  intro j i
  letI : IsProbabilityMeasure P := X.isProbability
  dsimp
  obtain ⟨hMI, _, hM2I, _⟩ :=
    avram_a24_original_canonical_clipped_gaussian_grid_conditional_first_second_moments
      X hν σ hσstop n hσbound j i
  constructor
  · exact hMI.bdd_mul (hGmeas j i) (hGB j i)
  constructor
  · simpa only [mul_one] using
      ((integrable_const (1 : ℝ)).bdd_mul (hHmeas j i) (hHB j i))
  · exact hM2I.bdd_mul (hHmeas j i) (hHB j i)
