-- Prove2me | solution 1 for ErdosPosa.wt_pred
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:26:37.275444+00:00
-- url     : https://prove2.me/submissions/6bbddada-d26b-4bbb-aec2-987315441cdb

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPShort
public import Definitions.Def_ErdosPosaLib_EPPacking

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
theorem _root_.solution (d : ℕ) (hd : 1 ≤ d) : wt d ≤ wt (d - 1) + 1 := by
  unfold wt; split_ifs <;> omega
end ErdosPosa
