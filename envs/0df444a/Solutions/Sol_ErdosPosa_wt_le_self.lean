-- Prove2me | solution 1 for ErdosPosa.wt_le_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:35:24.032604+00:00
-- url     : https://prove2.me/submissions/90633911-26e8-4332-aa87-1f315f89e64f

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
theorem _root_.solution (d : ℕ) : wt d ≤ d := by unfold wt; split_ifs <;> omega
end ErdosPosa
