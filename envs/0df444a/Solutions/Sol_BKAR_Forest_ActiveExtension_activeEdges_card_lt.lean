-- Prove2me | solution 1 for BKAR.Forest.ActiveExtension.activeEdges_card_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:55:38.340971+00:00
-- url     : https://prove2.me/submissions/9738ec55-dc06-4659-9410-ccf4bb54ca20

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
import Theorems.Thm_BKAR_Forest_EdgeExtension_activeEdges_card_lt

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveExtension
variable {F : Forest V} {e : Edge V}
namespace BKAR.Forest.ActiveExtension
theorem _root_.solution (h : ActiveExtension F e) :
    h.forest.activeEdges.card < F.activeEdges.card :=
  h.extension.activeEdges_card_lt
end BKAR.Forest.ActiveExtension
