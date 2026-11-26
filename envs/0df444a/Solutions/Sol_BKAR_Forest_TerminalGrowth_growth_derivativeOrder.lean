-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.growth_derivativeOrder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:24:01.225179+00:00
-- url     : https://prove2.me/submissions/5085e777-bb7d-4d46-bba3-b8f2f99c9d86

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}
namespace BKAR.Forest.TerminalGrowth
theorem _root_.solution (data : TerminalGrowth F) :
    data.growth.derivativeOrder = data.order.reverse :=
  rfl
end BKAR.Forest.TerminalGrowth
