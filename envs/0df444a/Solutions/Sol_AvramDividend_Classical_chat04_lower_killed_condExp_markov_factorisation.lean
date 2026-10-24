-- Prove2me | solution 1 for AvramDividend.Classical.chat04_lower_killed_condExp_markov_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:00:17.702725+00:00
-- url     : https://prove2.me/submissions/ed88abe1-eed9-495f-9cde-33c4fabb4417

import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_lower_survival_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_lower_killing_indicator_factorisation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! The conditional expectation of any truly killed future reward factors
into historical ruin survival and the conditional expectation of the
future-killed reward. Only its latter integrability is assumed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) (f : Ω → ℝ)
    (hf : Integrable
      (({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator f) P) :
    P[({ω | ∀ v : ℝ≥0, v ≤ u → 0 ≤ x + X.X v ω}).indicator f | 𝓕 s] =ᵐ[P]
      ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
        (P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
          0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator f | 𝓕 s]) := by
  let A : Set Ω := {ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}
  let B : Set Ω := {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
    0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}
  let D : Set Ω := {ω | ∀ v : ℝ≥0, v ≤ u → 0 ≤ x + X.X v ω}
  have hAeq : A = {ω | ∀ v : ℝ≥0, v ≤ s → ¬ X.X v ω < -x} := by
    ext ω
    simp only [A, Set.mem_setOf_eq]
    constructor
    · intro h v hv
      have hp := h v hv
      exact not_lt.mpr (by linarith)
    · intro h v hv
      have hp := le_of_not_gt (h v hv)
      linarith
  have hA : MeasurableSet[𝓕 s] A := by
    rw [hAeq]
    exact AvramDividend.Classical.chat03_lower_survival_filtration_measurable
      X τ hCover (-x) s
  have hIndicator : D.indicator f = A.indicator (B.indicator f) := by
    simpa only [D, A, B] using
      (AvramDividend.Classical.chat04_lower_killing_indicator_factorisation
        X x s u hsu f)
  change P[D.indicator f | 𝓕 s] =ᵐ[P]
    A.indicator (P[B.indicator f | 𝓕 s])
  rw [hIndicator]
  exact condExp_indicator hf hA
