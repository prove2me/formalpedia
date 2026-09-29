-- Prove2me | solution 1 for Esgk.distinct_distances_deficiency_quintic_nat_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-14T02:18:30.441412+00:00
-- url     : https://prove2.me/submissions/d7717b2d-425c-4623-aca2-24a5c700a63b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Theorems.Thm_Esgk_distinct_distances_deficiency_threshold_alternatives
import Theorems.Thm_Esgk_five_threshold_branches_quintic

open EuclideanGeometry Filter Esgk

theorem solution :
    ∃ A : ℕ, 0 < A ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ p : Config n,
          Function.Injective p →
          InGeneralPosition (Config.toFinset p) →
          ∃ σ : ℕ,
            (n - 1) + σ = 3 * distinctDistances (Config.toFinset p) ∧
            n ≤ A * (σ + 1) ^ 5 := by
  rcases distinct_distances_deficiency_threshold_alternatives with
    ⟨T, C, hT, _hC, hbranches⟩
  let A := max 3 (max (128 * T) (32 * C))
  have hA : 0 < A := by simp [A]
  refine ⟨A, hA, hbranches.mono ?_⟩
  intro n hn p hp hgp
  rcases hn p hp hgp with ⟨σ, hσ, hcases⟩
  refine ⟨σ, hσ, ?_⟩
  exact five_threshold_branches_quintic n (σ + 1) T C (by omega) hT hcases
