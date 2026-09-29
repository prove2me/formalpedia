-- Prove2me | solution 1 for Esgk.distinct_distances_one_sixth_excess
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-13T02:58:15.160973+00:00
-- url     : https://prove2.me/submissions/bb2dd6c9-cebc-44be-947d-07fc4ceb239b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
-/

import Theorems.Thm_Esgk_distinct_distances_one_fifth_excess

open EuclideanGeometry Filter
open Esgk

theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ p : Config n,
          Function.Injective p →
          InGeneralPosition (Config.toFinset p) →
          (n : ℝ) / 3 + c * Real.rpow (n : ℝ) (1 / 6 : ℝ) ≤
            (distinctDistances (Config.toFinset p) : ℝ) := by
  obtain ⟨c, hc, h_fifth⟩ := Esgk.distinct_distances_one_fifth_excess
  refine ⟨c, hc, ?_⟩
  filter_upwards [h_fifth, Filter.eventually_ge_atTop (1 : ℕ)] with n hn hn_one
  intro p hp hgp
  have hn_real : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn_one
  have h_exponents : (1 / 6 : ℝ) ≤ (1 / 5 : ℝ) := by
    norm_num
  have h_rpow :
      Real.rpow (n : ℝ) (1 / 6 : ℝ) ≤ Real.rpow (n : ℝ) (1 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hn_real h_exponents
  exact
    (add_le_add_right (mul_le_mul_of_nonneg_left h_rpow hc.le) ((n : ℝ) / 3)).trans
      (hn p hp hgp)
