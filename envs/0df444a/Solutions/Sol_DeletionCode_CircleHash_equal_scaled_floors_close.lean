-- Prove2me | solution 1 for DeletionCode.CircleHash.equal_scaled_floors_close
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:08.74198+00:00
-- url     : https://prove2.me/submissions/c7f03729-8ce5-40a5-93a7-ad3772b257b5

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_DeletionCode_CircleHash

set_option autoImplicit true
open DeletionCode DeletionCode.CircleHash
open scoped BigOperators
namespace DeletionCode.CircleHash
theorem _root_.solution (Q : ℕ) (hQ : 0 < Q) (a b : ℝ)
    (hlabel : ⌊(Q : ℝ) * a⌋ = ⌊(Q : ℝ) * b⌋) :
    |b - a| < 1 / (Q : ℝ) := by
  have hQr : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have h := Int.abs_sub_lt_one_of_floor_eq_floor hlabel.symm
  rw [← mul_sub, abs_mul, abs_of_pos hQr] at h
  apply (lt_div_iff₀ hQr).mpr
  simpa only [mul_comm] using h
end DeletionCode.CircleHash
