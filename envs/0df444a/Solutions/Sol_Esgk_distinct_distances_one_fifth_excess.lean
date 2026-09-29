-- Prove2me | solution 1 for Esgk.distinct_distances_one_fifth_excess
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-14T02:18:47.532114+00:00
-- url     : https://prove2.me/submissions/6f2b2cc8-7ab4-4a9e-9051-bbaf5828e17a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Theorems.Thm_Esgk_distinct_distances_deficiency_quintic_nat_bound
import Theorems.Thm_Esgk_eventual_one_fifth_excess_of_nat_deficiency_quintic

open EuclideanGeometry Filter Esgk

theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ p : Config n,
          Function.Injective p →
          InGeneralPosition (Config.toFinset p) →
          (n : ℝ) / 3 + c * Real.rpow (n : ℝ) (1 / 5 : ℝ) ≤
            (distinctDistances (Config.toFinset p) : ℝ) := by
  let Good : (n : ℕ) → Config n → Prop := fun _ p =>
    Function.Injective p ∧ InGeneralPosition (Config.toFinset p)
  let K : (n : ℕ) → Config n → ℕ := fun _ p =>
    distinctDistances (Config.toFinset p)
  have hquintic :
      ∃ A : ℕ, 0 < A ∧
        ∀ᶠ n : ℕ in Filter.atTop,
          ∀ p : Config n,
            Good n p →
            ∃ σ : ℕ, (n - 1) + σ = 3 * K n p ∧ n ≤ A * (σ + 1) ^ 5 := by
    rcases distinct_distances_deficiency_quintic_nat_bound with ⟨A, hA, hbound⟩
    refine ⟨A, hA, hbound.mono ?_⟩
    intro n hn p hp
    exact hn p hp.1 hp.2
  rcases eventual_one_fifth_excess_of_nat_deficiency_quintic Config Good K hquintic with
    ⟨c, hc, hfinal⟩
  refine ⟨c, hc, hfinal.mono ?_⟩
  intro n hn p hp hgp
  exact hn p ⟨hp, hgp⟩
