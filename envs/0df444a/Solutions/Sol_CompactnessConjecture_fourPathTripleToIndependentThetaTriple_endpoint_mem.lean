-- Prove2me | solution 1 for CompactnessConjecture.fourPathTripleToIndependentThetaTriple_endpoint_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/7125a407-4ad9-4d4a-b36d-cff2b9c61857

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace CompactnessConjecture
theorem _root_.solution
    (G : SimpleGraph V)
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (u : V)
    (endpoint : UnrelatedFourPathEndpoint G u)
    (base : {T : Finset V //
      T ∈ (commonSecondNeighborFinset G u
        (endpoint : V)).powersetCard 3}) :
    (endpoint : V) ∈ commonCenterFinset G
      (fourPathTripleToIndependentThetaTriple
        G hbip hfour hsix u endpoint base).val := by
  change (endpoint : V) ∈ commonCenterFinset G base.val
  apply (mem_commonCenterFinset G base.val (endpoint : V)).mpr
  intro x hx
  have hsubset := (Finset.mem_powersetCard.mp base.property).1
  exact commonNeighborRelated_symm
    ((mem_commonSecondNeighborFinset
      G u (endpoint : V) x).mp (hsubset hx)).2
end CompactnessConjecture
