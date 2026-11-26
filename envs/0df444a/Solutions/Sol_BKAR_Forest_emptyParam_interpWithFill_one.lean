-- Prove2me | solution 1 for BKAR.Forest.emptyParam_interpWithFill_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:24:01.010723+00:00
-- url     : https://prove2.me/submissions/b5870556-bc20-4cd4-b7b2-e00de401acb6

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
import Theorems.Thm_BKAR_Forest_emptyParam_interpWithFill

set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution :
    (Forest.empty V).interpWithFill emptyParam 1 = oneConfig :=
  emptyParam_interpWithFill 1
end BKAR.Forest
