-- Prove2me | solution 1 for AvramDividend.Classical.chat04_countable_grid_strict_survival_event_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T07:43:53.340272+00:00
-- url     : https://prove2.me/submissions/94d338a8-7896-4c15-986a-68dc87b7af6a

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_countable_inverse_nat_grid_exit_iff
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Any countable monitoring schedule containing all reciprocal-natural-grid
times detects *every* strict two-sided continuous-time exit. This turns the
accepted Chat03 grid-density theorem into an equality of survival events.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (lower upper : ℝ) :
    {ω | ∀ t : ℝ≥0, ¬ (X.X t ω < lower ∨ upper < X.X t ω)} =
      ⋂ j : ℕ,
        {ω | ¬ (X.X (τ j) ω < lower ∨ upper < X.X (τ j) ω)} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iInter]
  constructor
  · intro h j
    exact h (τ j)
  · intro h t
    by_contra hbad
    have hExit :
        ∃ r : ℝ≥0, X.X r ω < lower ∨ upper < X.X r ω :=
      ⟨t, hbad⟩
    obtain ⟨n, hn, k, hk⟩ :=
      (AvramDividend.Classical.chat03_countable_inverse_nat_grid_exit_iff
        X ω lower upper).mp hExit
    obtain ⟨j, hτ⟩ := hCover n hn k
    have hSurvive := h j
    rw [hτ] at hSurvive
    exact hSurvive hk
