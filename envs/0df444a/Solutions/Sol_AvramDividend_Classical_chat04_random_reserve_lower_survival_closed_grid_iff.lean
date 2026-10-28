-- Prove2me | solution 1 for AvramDividend.Classical.chat04_random_reserve_lower_survival_closed_grid_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T19:50:42.901896+00:00
-- url     : https://prove2.me/submissions/469ccccd-6dff-4c30-a513-7dc82ba18f3b

import Mathlib.Data.NNReal.Defs
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_lower_survival_dense_grid_iff
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Full-horizon nonruin is rational-grid survival plus a terminal check. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (T : ℝ≥0) :
    (∀ t : ℝ≥0, t ≤ T → 0 ≤ H ω + X.X t ω) ↔
      (∀ n : ℕ, 0 < n → ∀ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T →
          0 ≤ H ω + X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω) ∧
        0 ≤ H ω + X.X T ω := by
  constructor
  · intro hs
    refine ⟨?_, hs T le_rfl⟩
    intro n hn k hk
    exact hs _ (le_of_lt hk)
  · rintro ⟨hg, hT⟩ t ht
    rcases lt_or_eq_of_le ht with hlt | heq
    · exact (chat04_random_reserve_lower_survival_dense_grid_iff
        X H ω T).mpr hg t hlt
    · subst t
      exact hT
