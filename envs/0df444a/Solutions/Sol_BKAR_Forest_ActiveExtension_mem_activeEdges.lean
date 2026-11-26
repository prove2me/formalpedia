-- Prove2me | solution 1 for BKAR.Forest.ActiveExtension.mem_activeEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:33:59.586476+00:00
-- url     : https://prove2.me/submissions/b6969ef3-ea9b-42d5-9e5e-ee6be27d0f15

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
import Theorems.Thm_BKAR_Forest_EdgeExtension_mem_activeEdges

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveExtension
variable {F : Forest V} {e : Edge V}
namespace BKAR.Forest.ActiveExtension
theorem _root_.solution (h : ActiveExtension F e) :
    e ∈ F.activeEdges :=
  h.extension.mem_activeEdges
end BKAR.Forest.ActiveExtension
