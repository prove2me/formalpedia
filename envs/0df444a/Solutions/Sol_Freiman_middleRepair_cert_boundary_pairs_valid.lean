-- Prove2me | solution 1 for Freiman.middleRepair_cert_boundary_pairs_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-10T09:38:59.087804+00:00
-- url     : https://prove2.me/submissions/23103d6e-d7a1-4a6d-a59c-41c4d291fdf5

import Definitions.Def_Freiman_middleRepairLedger

open Freiman

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace M8Sep10BoundaryPairs

local instance (C : MiddleCertCatalog) (p : MiddleCertPair) (direction : ℤ) :
    Decidable (middleCertPairValid C p direction) := by
  unfold middleCertPairValid
  infer_instance
local instance (C : MiddleCertCatalog) (p : MiddleCertProof) :
    Decidable (middleCertProofValid C p) := by
  cases p <;> unfold middleCertProofValid <;> infer_instance
local instance (C : MiddleCertCatalog) (r : MiddleCertRecord) :
    Decidable (middleCertRecordValid C r) := by
  unfold middleCertRecordValid
  infer_instance
local instance (C : MiddleCertCatalog) (g : MiddleCertGoal) (sp : MiddleCertSpec) :
    Decidable (middleCertGoalMatches C g sp) := by
  unfold middleCertGoalMatches
  infer_instance
local instance (C : MiddleCertCatalog) (goal branch : ℕ) (parent : ℤ) :
    Decidable (middleCertRecorded C goal branch parent) := by
  unfold middleCertRecorded
  infer_instance

local instance (C : MiddleCertCatalog) (redirects : List MiddleRepairRedirect)
    (rec : MiddleCertRecord) (parent : ℤ) : Decidable (middleRepairRecordValid C redirects rec parent) := by
  unfold middleRepairRecordValid
  infer_instance

private def selected : List MiddleCertRecord := [
  ⟨1,24,[-1],917⟩,
  ⟨1,29,[-1],917⟩,
  ⟨11,4,[24,25,26,27,28,29,30,31],917⟩,
  ⟨11,6,[24,25,26,27,28,29,30,31],917⟩,
  ⟨92,2,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩,
  ⟨92,3,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩,
  ⟨92,4,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩,
  ⟨92,5,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩,
  ⟨92,6,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩,
  ⟨92,7,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩,
  ⟨96,8,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩,
  ⟨96,9,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩]

private def selectedKeys : List (ℕ × ℕ × ℕ) :=
  selected.map fun r => (r.goal, r.branch, r.proof)

private theorem key_complete :
    ∀ r ∈ middleCertData.records, (r.goal, r.branch, r.proof) ∈ selectedKeys → r ∈ selected := by
  decide +kernel

private theorem redirects_keys :
    ∀ a ∈ middleRepairRedirects, (a.goal, a.branch, a.originalProof) ∈ selectedKeys := by
  decide +kernel

private theorem selected_valid :
    ∀ rec ∈ selected, ∀ parent ∈ rec.parents,
      middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) ≠ none →
      middleRepairRecordValid middleCertData middleRepairRedirects rec parent := by
  decide +kernel

private theorem found_selected (rec : MiddleCertRecord) (hr : rec ∈ middleCertData.records)
    (parent : ℤ) (hf : middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) ≠ none) :
    rec ∈ selected := by
  cases he : middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) with
  | none => exact False.elim (hf he)
  | some a =>
    have ha := List.mem_of_find?_eq_some he
    have hm := List.find?_some he
    have hm' : a.goal = rec.goal ∧ a.branch = rec.branch ∧ a.parent = parent ∧ a.originalProof = rec.proof := by
      simpa only [middleRepairRedirectMatches, decide_eq_true_eq] using hm
    have hk := redirects_keys a ha
    rw [hm'.1, hm'.2.1, hm'.2.2.2] at hk
    exact key_complete rec hr hk

end M8Sep10BoundaryPairs

theorem solution :
    ∀ rec ∈ middleCertData.records, ∀ parent ∈ rec.parents, middleRepairRedirects.find? (fun a => middleRepairRedirectMatches a rec parent) ≠ none → middleRepairRecordValid middleCertData middleRepairRedirects rec parent := by
  intro rec hr parent hp hf
  exact M8Sep10BoundaryPairs.selected_valid rec
    (M8Sep10BoundaryPairs.found_selected rec hr parent hf) parent hp hf

#print axioms solution
