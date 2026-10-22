-- Prove2me | solution 1 for GDGen3.pj_slope_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T06:22:04.632243+00:00
-- url     : https://prove2.me/submissions/0aa0cda4-4ae4-4ffc-824e-63479d9f9e03

import Mathlib
import Definitions.Def_GDGen3Base
import Theorems.Thm_GDGen3_pj_geometric
import Theorems.Thm_GDGen3_pow_slope_strictMono

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    StrictMono (fun n : ℕ => pj r (n + 1) / ((n : ℝ) + 1)) := by
  have hz : 1 < 1 / r ^ 2 := by
    apply (lt_div_iff₀ (by positivity : 0 < r ^ 2)).2
    have ht : r ^ 2 < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
    simpa using ht
  intro a b hab
  have h := pow_slope_strictMono (1 / r ^ 2) hz hab
  dsimp at h ⊢
  rw [pj_geometric r (ne_of_gt hr), pj_geometric r (ne_of_gt hr)]
  have he : ∀ k : ℕ, (((1 / r ^ 2) ^ (k + 1) - 1) / 2) / ((k : ℝ) + 1) =
      (((1 / r ^ 2) ^ (k + 1) - 1) / ((k : ℝ) + 1)) / 2 := by intro k; ring
  rw [he, he]
  exact div_lt_div_of_pos_right h (by norm_num)
