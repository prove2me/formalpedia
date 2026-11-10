-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss13_localise_original_two_bounded_sampled_gaussian_clock_values_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T09:09:04.228948+00:00
-- url     : https://prove2.me/submissions/36754a00-23c9-4413-b13b-6a8f184e1007

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (grid : ℕ → ℝ≥0)
    (𝓖 : Filtration ℕ mΩ)
    (α β : Ω → WithTop ℕ)
    (hα : IsStoppingTime 𝓖 α) (hβ : IsStoppingTime 𝓖 β)
    (hαβ : α ≤ β)
    (N : ℕ) (hN : ∀ ω, β ω ≤ (N : WithTop ℕ)) :
    Integrable (stoppedValue
      (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2) α) P ∧
    Integrable (stoppedValue
      (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2) β) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hval (i : ℕ) :
      Integrable (fun _ : Ω => (grid i : ℝ) * X.σ ^ 2) P :=
    integrable_const _
  refine ⟨?_, ?_⟩
  · exact integrable_stoppedValue ℕ hα hval
      (fun ω => le_trans (hαβ ω) (hN ω))
  · exact integrable_stoppedValue ℕ hβ hval hN
