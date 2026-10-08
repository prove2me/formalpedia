-- Prove2me | solution 1 for ConvexOptAlg.NesterovSmooth.lam_ge_half
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:13:33.654333+00:00
-- url     : https://prove2.me/submissions/0be8de3a-c7ac-405e-8405-3a888d0e361e

import Mathlib
import Definitions.Def_ConvexOptAlg_NesterovSmooth_Defs
open scoped InnerProductSpace

open ConvexOptAlg.NesterovSmooth in
theorem lam_succ_ge_aux_722e7b42 (n : ℕ) : lam n + 1 / 2 ≤ lam (n + 1) := by
  rw [lam.eq_2]
  have h1 : 2 * lam n ≤ Real.sqrt (1 + 4 * lam n ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  linarith

open ConvexOptAlg.NesterovSmooth in
theorem lam_ge_aux_722e7b42 (n : ℕ) : ((n : ℝ) + 2) / 2 ≤ lam (n + 1) := by
  induction n with
  | zero =>
    have h := lam_succ_ge_aux_722e7b42 0
    have h0 : lam 1 = 1 := by
      rw [lam.eq_2, lam.eq_1]
      norm_num
    rw [h0]
    norm_num
  | succ k ih =>
    have h := lam_succ_ge_aux_722e7b42 (k + 1)
    push_cast
    linarith

open ConvexOptAlg.NesterovSmooth in
theorem solution (t : ℕ) (ht : 2 ≤ t) : (t : ℝ) / 2 ≤ lam (t - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 2 := ⟨t - 2, by omega⟩
  have h := lam_ge_aux_722e7b42 n
  have e : n + 2 - 1 = n + 1 := by omega
  rw [e]
  push_cast
  linarith
