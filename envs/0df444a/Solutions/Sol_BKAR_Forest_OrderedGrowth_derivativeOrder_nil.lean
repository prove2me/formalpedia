-- Prove2me | solution 1 for BKAR.Forest.OrderedGrowth.derivativeOrder_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:41:22.26425+00:00
-- url     : https://prove2.me/submissions/ec32f9e3-a373-49a9-90b6-a4ff3e1a21e6

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.OrderedGrowth
theorem _root_.solution (F : Forest V) :
    (OrderedGrowth.nil F).derivativeOrder = [] :=
  rfl
end BKAR.Forest.OrderedGrowth
