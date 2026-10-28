-- Prove2me | solution 1 for AvramDividend.Classical.finite_grid_lower_survival_min_equiv
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:49:34.476978+00:00
-- url     : https://prove2.me/submissions/b3c4af35-3074-4fd0-9eeb-b3eb4d5bab4a

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : Finset ℕ) (hs : s.Nonempty)
    (τ : ℕ → ℝ≥0) (ω : Ω) (x : ℝ) :
    (∀ k : ℕ, k ∈ s → 0 ≤ x + X.X (τ k) ω) ↔
      0 ≤ x + s.inf' hs (fun k => X.X (τ k) ω) := by 
  constructor
  · intro h
    obtain ⟨k, hk, he⟩ := Finset.exists_mem_eq_inf' hs (fun k => X.X (τ k) ω)
    rw [he]; exact h k hk
  · intro h k hk
    have := Finset.inf'_le (fun k => X.X (τ k) ω) hk
    linarith
