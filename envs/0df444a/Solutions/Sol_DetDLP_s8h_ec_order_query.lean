-- Prove2me | solution 1 for DetDLP.s8h_ec_order_query
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T10:03:31.391802+00:00
-- url     : https://prove2.me/submissions/f7576f80-3b65-4360-b718-fb5e2cd263ca

import Definitions.Def_DetDLP_S8H0_GateDispatchEq
import Definitions.Def_DetDLP_S8H0_OrderMake
import Definitions.Def_DetDLP_S8H0_GraphDegree
import Theorems.Thm_DetDLP_w3_m5_modmul_r2

set_option autoImplicit false
open DetDLP DetDLP.S8H0

theorem solution : DetDLP.S8C.GadgetLaws → DetDLP.S8C.TagSpec [0] := by
  intro _
  apply OrderPacket.tagIntro OrderMake.make GateDispatchEq.exactPort OrderMake.make_poly GateDispatchEq.exactPort_poly
  intro p _ _ E _
  let c := GateSemantics.coeff E
  let A := PointGraph.layout p c
  let t := PointGraph.tests p c
  apply OrderPacket.ofLayout E w3_m5_modmul_r2 A t (GraphBudget.gateBudget p c) OrderMake.make GateDispatchEq.exactPort
  · exact (w3_factorEquiv A t).symm.trans ((S8J.CircuitRealizes.decode (PointGraph.C p c) (PointGraph.W p c)).trans ((PointGraph.logicalEquiv E).trans (SignalBank.witnessEquiv E)))
  · exact GraphBudget.edgeBudget p c
  · exact GraphDegree.degree p c
  · exact OrderMake.make_word p E
  · exact GateDispatchEq.exactPort_eval E
