-- Prove2me | solution 1 for AvramDividend.Classical.nonnegative_martingale_survival_mass_antitone
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T21:46:50.260933+00:00
-- url     : https://prove2.me/submissions/ac2f34f6-903e-4461-be01-7bf0d2e2bc55

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P 𝓕]
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M 𝓕 P)
    (hNonneg : ∀ t : ℝ≥0, 0 ≤ᵐ[P] M t)
    (S : ℝ≥0 → Set Ω)
    (hS : ∀ t, MeasurableSet[𝓕 t] (S t))
    (hMono : ∀ t u, t ≤ u → S u ⊆ S t)
    (t u : ℝ≥0) (htu : t ≤ u) :
    (∫ ω, (S u).indicator (M u) ω ∂P) ≤
      (∫ ω, (S t).indicator (M t) ω ∂P) := by
  have hmS : ∀ s, MeasurableSet (S s) := fun s => 𝓕.le s _ (hS s)
  rw [integral_indicator (hmS u), integral_indicator (hmS t),
    hM.setIntegral_eq htu (hS t)]
  exact setIntegral_mono_set (hM.integrable u).integrableOn
    (ae_restrict_of_ae (hNonneg u)) (Filter.Eventually.of_forall (hMono t u htu))
