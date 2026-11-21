-- Prove2me | solution 1 for BFWFluidLimit.scaled_variance_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T02:46:45.122812+00:00
-- url     : https://prove2.me/submissions/1f546960-540a-42a3-b99f-ec88d294e864

import Mathlib

theorem solution (u w : ℝ → ℝ) (t p : ℝ) (ht : t ≠ 0)
    (hu : HasDerivAt u ((p - u t) / t) t)
    (hw : HasDerivAt w ((p ^ 2 - w t) / t) t) :
    HasDerivAt (fun s => s * (w s - u s ^ 2)) ((p - u t) ^ 2) t := by
  have h1 := hu.mul hu
  have h2 := hw.sub h1
  have h3 := (hasDerivAt_id t).mul h2
  convert h3 using 1
  · rfl
  · rfl
  · funext s; simp [Pi.mul_apply, pow_two]
  · simp only [Pi.sub_apply, Pi.mul_apply, id_eq]
    field_simp
    ring
