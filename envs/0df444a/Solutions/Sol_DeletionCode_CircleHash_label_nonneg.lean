-- Prove2me | solution 1 for DeletionCode.CircleHash.label_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:07.664427+00:00
-- url     : https://prove2.me/submissions/ed95c1cc-2f30-4b64-b5d8-0cf98f3dfdf8

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Algebra.Order.Floor.Ring
import Definitions.Def_DeletionCode_CircleHash
import Theorems.Thm_DeletionCode_CircleHash_representative_mem

set_option autoImplicit true
open DeletionCode DeletionCode.CircleHash
open scoped BigOperators
namespace DeletionCode.CircleHash
theorem _root_.solution (Q : ℕ) (z : UnitAddCircle) : 0 ≤ label Q z := by
  apply Int.floor_nonneg.mpr
  exact mul_nonneg (Nat.cast_nonneg Q) (representative_mem z).1
end DeletionCode.CircleHash
