-- Prove2me | solution 1 for BKAR.Forest.grownForestForSupportOrder_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:55:54.894369+00:00
-- url     : https://prove2.me/submissions/08f5dbbb-0610-42c5-a54b-25cfbf09036c

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge
import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
import Theorems.Thm_P2M_BKAR_Forest_exists_followOrder__eq_some_support_of_mem_edgeSetOrders_94b5d7b04ff1


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges}) :
    (grownForestForSupportOrder choices I order).support = I :=
  (Classical.choose_spec
    (exists_followOrder?_eq_some_support_of_mem_edgeSetOrders
      choices order.property)).2
end BKAR.Forest
