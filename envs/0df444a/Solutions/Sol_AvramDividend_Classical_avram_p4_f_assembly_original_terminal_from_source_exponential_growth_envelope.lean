-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_terminal_from_source_exponential_growth_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:51:48.420193+00:00
-- url     : https://prove2.me/submissions/94f3d965-5a77-4c98-bd69-87e041a9b9a1

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_stopped_exponential_payoff_le_raw_Levy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact original stopped terminal growth bound via raw source exponential. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (w : ℝ → ℝ) (q θ K : ℝ) (hθ : 0 ≤ θ) (hK : 0 ≤ K)
    (hwGrowth : ∀ y : ℝ, w y ≤ K * Real.exp (θ * y))
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    ∀ ω, Term ω ≤
      Real.exp (-(q * (τ ω : ℝ))) *
        (K * Real.exp (θ * (x + X.X (τ ω) ω))) := by
  have hSource :=
    avram_p4_f_assembly_original_stopped_exponential_payoff_le_raw_Levy
      X C x D hD τ W hW θ hθ
  intro ω
  calc
    Term ω =
        Real.exp (-(q * (τ ω : ℝ))) * w (W ω) := hTerm ω
    _ ≤ Real.exp (-(q * (τ ω : ℝ))) *
          (K * Real.exp (θ * W ω)) :=
      mul_le_mul_of_nonneg_left (hwGrowth (W ω))
        (Real.exp_pos _).le
    _ ≤ Real.exp (-(q * (τ ω : ℝ))) *
          (K * Real.exp (θ * (x + X.X (τ ω) ω))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hSource ω) hK)
        (Real.exp_pos _).le
