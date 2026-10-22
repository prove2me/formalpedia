-- Prove2me | solution 2 for GDGen3.referenceXi_quad
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T11:38:01.637576+00:00
-- url     : https://prove2.me/submissions/cd9fbd07-a9db-407a-b061-b0cf72611089

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_pj_pos
import Theorems.Thm_GDGen3_PiS_closed
import Theorems.Thm_GDGen3_rootPoly_expanded

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (i : ℕ) :
    rootPoly r (1 + r) i (referenceXi r i) = 0 := by
  have hr2 : 1 - r ^ 2 ≠ 0 := by
    have ht : r ^ 2 < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
    linarith
  have hp : pj r (i + 1) ≠ 0 := ne_of_gt (pj_pos r hr hr1 (i + 1) (by omega))
  rw [rootPoly_expanded r hr hr1]
  unfold referenceXi
  rw [PiS_closed r hr hr1 i]
  unfold pj
  have he : r ^ (2 * i) = (r ^ i) ^ 2 := by rw [Nat.mul_comm 2 i, pow_mul]
  have he1 : r ^ (2 * (i + 1)) = (r ^ i * r) ^ 2 := by
    rw [Nat.mul_comm 2 (i + 1), pow_mul, pow_succ r i]
  rw [he, he1, pow_succ r i]
  set b := r ^ i
  have hbpos : 0 < b := pow_pos hr i
  have hbp : 1 - (b * r) ^ 2 ≠ 0 := by
    have ht : r ^ (2 * (i + 1)) < 1 := pow_lt_one₀ (le_of_lt hr) hr1 (by omega)
    rw [he1] at ht
    change (b * r) ^ 2 < 1 at ht
    linarith
  field_simp [hbp]
  ring
