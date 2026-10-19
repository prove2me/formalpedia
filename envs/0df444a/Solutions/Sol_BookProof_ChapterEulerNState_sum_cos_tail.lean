-- Prove2me | solution 1 for BookProof.ChapterEulerNState.sum_cos_tail
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:57:15.095663+00:00
-- url     : https://prove2.me/submissions/314dc1f4-ed16-42d1-8dbc-4b26f758c12c

import Mathlib
import Definitions.Def_ChapterEulerNState
-- Generated from ChapterEulerNState.lean — theorem BookProof.ChapterEulerNState.sum_cos_tail
open BookProof.ChapterEulerNState


open scoped BigOperators


theorem solution (θ : ℕ → ℝ) (m : ℕ) :
    ∑ k ∈ Finset.range m, tailProd θ k * Real.cos (θ k) ^ 2
      = 1 - tailProd θ m := by
  have step : ∀ k, tailProd θ k * Real.cos (θ k) ^ 2 = tailProd θ k - tailProd θ (k + 1) := by
    intro k
    simp only [tailProd, Finset.prod_range_succ]
    have := Real.sin_sq_add_cos_sq (θ k)
    linear_combination (∏ i ∈ Finset.range k, Real.sin (θ i) ^ 2) * this
  simp_rw [step]
  rw [Finset.sum_range_sub']
  simp [tailProd]

