-- Prove2me | solution 1 for FixedNumerator.one_sub_norm_le_norm_one_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:41:49.464822+00:00
-- url     : https://prove2.me/submissions/b2965383-082a-4b6a-be9d-67ec9a2d5782

module
public import Definitions.Def_FixedNumerator_Cases
public import Definitions.Def_FixedNumerator_Determinant

set_option autoImplicit true
@[expose] public section
public section
open Complex Real
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution (t : ℂ) : 1 - ‖t‖ ≤ ‖1 + t‖ := by
  have := norm_sub_norm_le (1 : ℂ) (-t)
  simpa [sub_neg_eq_add] using this
end FixedNumerator
