-- Prove2me | solution 1 for Freiman.middleRepair_cert_branch_identity
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-10T09:44:27.917345+00:00
-- url     : https://prove2.me/submissions/f6cb82bc-a3af-4390-85bf-885c4d552a66

import Definitions.Def_Freiman_middleRepairLedger

open Freiman

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace M8Sep10BranchIdentity

private theorem equal_fst (w : LowerPair) (upper parity incoming : Bool) :
    (middleRepairCertEqualCases w upper parity incoming).map Prod.fst =
      (middleCertEqualCases w upper parity).map Prod.fst := by
  rfl

private theorem endpoint_fst (w : LowerPair) (upper parity incoming : Bool) :
    (middleRepairCertEndpointCases w upper parity incoming).map Prod.fst =
      (middleCertEndpointCases w upper parity).map Prod.fst := by
  by_cases h : middleCertOdd w parity false = middleCertOdd w parity true
  · simp only [middleRepairCertEndpointCases, middleCertEndpointCases, if_pos h, equal_fst]
  · simp only [middleRepairCertEndpointCases, middleCertEndpointCases, if_neg h,
      middleRepairCertNormals, middleCertNormals, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.map_append, List.map_map, Function.comp_def]
    simp only [equal_fst]

private theorem comparisons_projection (xs ys : List LowerHistoryEndCase) (parity : Bool) :
    (xs.flatMap fun (x,cx) => ys.map fun (y,cy) =>
      (cx ++ cy, middleCertGreater parity x y)).map Prod.snd =
    (xs.map Prod.fst).flatMap fun x => (ys.map Prod.fst).map fun y => middleCertGreater parity x y := by
  simp only [List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]

private theorem catalog_endpoints :
    ∀ e ∈ middleCertData.endpoints,
      (middleCertActualCases middleCertData e).map Prod.fst =
      (middleCertEndpointCases e.words e.upper e.parity).map Prod.fst := by
  decide +kernel

private theorem goal_indices :
    ∀ g ∈ middleCertData.goals,
      g.first - 1 < middleCertData.endpoints.length ∧
      g.second - 1 < middleCertData.endpoints.length ∧
      (middleCertEndpoint middleCertData g.first).parity = middleCertParity g.family ∧
      (middleCertEndpoint middleCertData g.second).parity = middleCertParity g.family := by
  decide +kernel

private theorem endpoint_mem (C : MiddleCertCatalog) (i : ℕ)
    (hi : i - 1 < C.endpoints.length) : middleCertEndpoint C i ∈ C.endpoints := by
  simp only [middleCertEndpoint, List.getElem?_eq_getElem hi, Option.getD_some]
  exact List.getElem_mem hi

private theorem goal_projection (g : MiddleCertGoal) (hg : g ∈ middleCertData.goals) :
    (middleRepairCertGoalBranches middleCertData g).map Prod.snd =
      (middleCertGoalBranches middleCertData g).map Prod.snd := by
  have hi := goal_indices g hg
  have hfirst := catalog_endpoints _ (endpoint_mem middleCertData g.first hi.1)
  have hsecond := catalog_endpoints _ (endpoint_mem middleCertData g.second hi.2.1)
  rw [hi.2.2.1] at hfirst
  rw [hi.2.2.2] at hsecond
  simp only [middleRepairCertGoalBranches, middleRepairCertCompare, middleCertGoalBranches,
    comparisons_projection, endpoint_fst]
  rw [← hfirst, ← hsecond]

end M8Sep10BranchIdentity

theorem solution :
    middleRepairBranchIdentity middleCertData := by
  constructor
  · exact M8Sep10BranchIdentity.goal_projection
  · intro parity
    cases parity <;> decide +kernel

#print axioms solution
