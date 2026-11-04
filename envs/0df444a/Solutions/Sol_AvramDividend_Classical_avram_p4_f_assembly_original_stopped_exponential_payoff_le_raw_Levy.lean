-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_stopped_exponential_payoff_le_raw_Levy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:33:58.292324+00:00
-- url     : https://prove2.me/submissions/e88e6f52-5b81-4c54-9727-aa549c2b9b1f

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_stopped_W_le_source_X
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual original stopped dividend reserve has exponential
    positive-moment envelope given by the raw source Lévy path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    ∀ ω, Real.exp (θ * W ω) ≤ Real.exp (θ * (x + X.X (τ ω) ω)) := by
  have hWraw :=
    avram_p4_f_assembly_original_stopped_W_le_source_X
      X C x D hD τ W hW
  intro ω
  exact Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (hWraw ω) hθ)