-- Prove2me | solution 1 for BKAR.Forest.emptyParam_standardInterp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:23:53.346264+00:00
-- url     : https://prove2.me/submissions/e47f5e4b-5237-4c9e-ad07-50729d0235d8

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
import Theorems.Thm_BKAR_Forest_empty_standardInterp

set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution :
    (Forest.empty V).standardInterp emptyParam = zeroConfig :=
  empty_standardInterp emptyParam
end BKAR.Forest
