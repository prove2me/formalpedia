-- Prove2me | solution 1 for BKAR.Forest.emptyParam_interpWithFill
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:18:29.644089+00:00
-- url     : https://prove2.me/submissions/072f49da-54de-42ba-b99a-f911fd224fc1

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
import Theorems.Thm_BKAR_Forest_empty_interpWithFill

set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (t : ℝ) :
    (Forest.empty V).interpWithFill emptyParam t = constantConfig t :=
  empty_interpWithFill emptyParam t
end BKAR.Forest
