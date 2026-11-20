-- Prove2me | solution 1 for DeletionCode.CircleHash.label_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:08.223904+00:00
-- url     : https://prove2.me/submissions/92bcb4f2-edc5-414d-b125-e2058551bdc2

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_DeletionCode_CircleHash
import Theorems.Thm_DeletionCode_CircleHash_representative_mem

set_option autoImplicit true
open DeletionCode DeletionCode.CircleHash
open scoped BigOperators
namespace DeletionCode.CircleHash
theorem _root_.solution (Q : ℕ) (hQ : 0 < Q) (z : UnitAddCircle) : label Q z < (Q : ℤ) := by
  apply Int.floor_lt.mpr
  have hQr : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have h := mul_lt_mul_of_pos_left (representative_mem z).2 hQr
  simpa only [mul_one, Int.cast_natCast] using h
end DeletionCode.CircleHash
