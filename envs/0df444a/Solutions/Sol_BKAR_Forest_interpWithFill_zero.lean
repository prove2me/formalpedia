-- Prove2me | solution 1 for BKAR.Forest.interpWithFill_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:23:51.37469+00:00
-- url     : https://prove2.me/submissions/c60ee870-3817-4dc1-83f6-5f0d3ca3d8eb

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation

set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) (u : F.EdgeParam → ℝ) :
    F.interpWithFill u 0 = F.standardInterp u :=
  rfl
end BKAR.Forest
