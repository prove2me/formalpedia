-- Prove2me | solution 2 for Freiman.middle_cert_family_equal_II_a_valid
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T16:32:03.704536+00:00
-- url     : https://prove2.me/submissions/050d9a32-83e2-4637-abcb-332ae7e32db0

import Definitions.Def_Freiman_middleCertData
import Mathlib.Tactic.FinCases

open Freiman

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

local instance (C : MiddleCertCatalog) (p : MiddleCertPair) (direction : ℤ) :
    Decidable (middleCertPairValid C p direction) := by
  unfold middleCertPairValid
  infer_instance
local instance (C : MiddleCertCatalog) (p : MiddleCertProof) :
    Decidable (middleCertProofValid C p) := by
  cases p <;> unfold middleCertProofValid <;> infer_instance
local instance (C : MiddleCertCatalog) (g : MiddleCertGoal) (sp : MiddleCertSpec) :
    Decidable (middleCertGoalMatches C g sp) := by
  unfold middleCertGoalMatches
  infer_instance
local instance (C : MiddleCertCatalog) (goal branch : ℕ) (parent : ℤ) :
    Decidable (middleCertRecorded C goal branch parent) := by
  unfold middleCertRecorded
  infer_instance

namespace FastFamily5

/-- Threshold-index level image of `LowerHistoryComparison`. -/
private inductive RefComparison where
  | automatic
  | impossible
  | bound (b : MiddleCertBoundRef)
  deriving DecidableEq

private def decodeComparison : RefComparison → LowerHistoryComparison
  | .automatic => .automatic
  | .impossible => .impossible
  | .bound b => .bound (middleCertBound middleCertData b)

private def decodeBranch (p : List MiddleCertBoundRef × RefComparison) :
    List CertBound × LowerHistoryComparison :=
  (middleCertBounds middleCertData p.1, decodeComparison p.2)

private def refComplement (b : MiddleCertBoundRef) : MiddleCertBoundRef :=
  ⟨!b.lower, !b.strict, b.threshold⟩

private theorem decode_auto {x : RefComparison} (h : decodeComparison x = .automatic) :
    x = RefComparison.automatic := by
  cases x <;> simp_all [decodeComparison]

private theorem getD_mem {α : Type} (l : List (List α)) (j : ℕ) (r : α)
    (h : r ∈ l[j]?.getD []) : ∃ rs ∈ l, r ∈ rs := by
  cases hh : l[j]? with
  | none => rw [hh] at h; simp at h
  | some rs =>
    refine ⟨rs, List.mem_iff_getElem?.mpr ⟨j, hh⟩, ?_⟩
    rw [hh] at h
    simpa using h

private def branches_83 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨true,false,603⟩,⟨false,false,633⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.automatic),
([⟨true,false,603⟩,⟨false,false,633⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,false,603⟩,⟨false,false,633⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.automatic),
([⟨true,false,603⟩,⟨false,false,633⟩,⟨true,true,221⟩,⟨true,true,591⟩,⟨false,false,215⟩],.automatic),
([⟨true,false,603⟩,⟨false,false,633⟩,⟨true,false,535⟩,⟨true,true,215⟩,⟨false,false,221⟩],.automatic),
([⟨true,false,603⟩,⟨false,false,633⟩,⟨true,true,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,false,603⟩,⟨false,false,633⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,false,603⟩,⟨false,false,633⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.impossible),
([⟨false,false,633⟩,⟨false,true,603⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.impossible),
([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,true,221⟩,⟨true,true,591⟩,⟨false,false,215⟩],.bound ⟨true,false,538⟩),
([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,false,535⟩,⟨true,true,215⟩,⟨false,false,221⟩],.impossible),
([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,true,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.impossible),
([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.bound ⟨true,false,538⟩),
([⟨true,true,633⟩,⟨false,false,666⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.bound ⟨false,false,580⟩),
([⟨true,true,633⟩,⟨false,false,666⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,633⟩,⟨false,false,666⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,633⟩,⟨false,false,666⟩,⟨true,true,221⟩,⟨true,true,591⟩,⟨false,false,215⟩],.automatic),
([⟨true,true,633⟩,⟨false,false,666⟩,⟨true,false,535⟩,⟨true,true,215⟩,⟨false,false,221⟩],.bound ⟨false,false,580⟩),
([⟨true,true,633⟩,⟨false,false,666⟩,⟨true,true,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,633⟩,⟨false,false,666⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,633⟩,⟨false,false,666⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,true,633⟩,⟨true,true,666⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.bound ⟨false,false,763⟩),
([⟨true,true,633⟩,⟨true,true,666⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.bound ⟨false,false,639⟩),
([⟨true,true,633⟩,⟨true,true,666⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.bound ⟨false,false,560⟩),
([⟨true,true,633⟩,⟨true,true,666⟩,⟨true,true,221⟩,⟨true,true,591⟩,⟨false,false,215⟩],.automatic),
([⟨true,true,633⟩,⟨true,true,666⟩,⟨true,false,535⟩,⟨true,true,215⟩,⟨false,false,221⟩],.bound ⟨false,false,763⟩),
([⟨true,true,633⟩,⟨true,true,666⟩,⟨true,true,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.bound ⟨false,false,639⟩),
([⟨true,true,633⟩,⟨true,true,666⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.bound ⟨false,false,560⟩),
([⟨true,true,633⟩,⟨true,true,666⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic)
]

private def branches_84 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨true,false,601⟩,⟨false,false,629⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨false,false,633⟩],.automatic),
([⟨true,false,601⟩,⟨false,false,629⟩,⟨false,false,634⟩,⟨false,false,633⟩,⟨false,true,601⟩],.impossible),
([⟨true,false,601⟩,⟨false,false,629⟩,⟨false,false,634⟩,⟨true,true,633⟩,⟨false,false,664⟩],.bound ⟨false,false,645⟩),
([⟨true,false,601⟩,⟨false,false,629⟩,⟨false,false,634⟩,⟨true,true,633⟩,⟨true,true,664⟩],.impossible),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,false,601⟩,⟨false,false,633⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨false,false,633⟩,⟨false,true,601⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,633⟩,⟨false,false,664⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,633⟩,⟨true,true,664⟩],.bound ⟨false,false,635⟩),
([⟨true,true,634⟩,⟨false,false,629⟩,⟨false,false,664⟩,⟨true,false,601⟩,⟨false,false,633⟩],.bound ⟨true,false,645⟩),
([⟨true,true,634⟩,⟨false,false,629⟩,⟨false,false,664⟩,⟨false,false,633⟩,⟨false,true,601⟩],.impossible),
([⟨true,true,634⟩,⟨false,false,629⟩,⟨false,false,664⟩,⟨true,true,633⟩,⟨false,false,664⟩],.automatic),
([⟨true,true,634⟩,⟨false,false,629⟩,⟨false,false,664⟩,⟨true,true,633⟩,⟨true,true,664⟩],.impossible),
([⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,629⟩,⟨true,false,601⟩,⟨false,false,633⟩],.automatic),
([⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,601⟩],.bound ⟨true,false,635⟩),
([⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,629⟩,⟨true,true,633⟩,⟨false,false,664⟩],.automatic),
([⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,629⟩,⟨true,true,633⟩,⟨true,true,664⟩],.automatic),
([⟨true,false,601⟩,⟨true,true,629⟩,⟨false,false,634⟩,⟨true,false,601⟩,⟨false,false,633⟩],.automatic),
([⟨true,false,601⟩,⟨true,true,629⟩,⟨false,false,634⟩,⟨false,false,633⟩,⟨false,true,601⟩],.impossible),
([⟨true,false,601⟩,⟨true,true,629⟩,⟨false,false,634⟩,⟨true,true,633⟩,⟨false,false,664⟩],.bound ⟨false,false,645⟩),
([⟨true,false,601⟩,⟨true,true,629⟩,⟨false,false,634⟩,⟨true,true,633⟩,⟨true,true,664⟩],.impossible),
([⟨true,true,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,false,601⟩,⟨false,false,633⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨false,false,633⟩,⟨false,true,601⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,633⟩,⟨false,false,664⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,633⟩,⟨true,true,664⟩],.bound ⟨false,false,635⟩),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,false,601⟩,⟨false,false,633⟩],.bound ⟨true,false,645⟩),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨false,false,633⟩,⟨false,true,601⟩],.impossible),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,633⟩,⟨false,false,664⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,633⟩,⟨true,true,664⟩],.impossible),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,false,601⟩,⟨false,false,633⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,633⟩,⟨false,true,601⟩],.bound ⟨true,false,635⟩),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,true,633⟩,⟨false,false,664⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,true,633⟩,⟨true,true,664⟩],.automatic)
]

private def branches_85 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨true,false,426⟩,⟨false,false,215⟩,⟨false,false,264⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.automatic),
([⟨true,false,426⟩,⟨false,false,215⟩,⟨false,false,264⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,false,426⟩,⟨false,false,215⟩,⟨false,false,264⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.automatic),
([⟨true,false,426⟩,⟨false,false,215⟩,⟨false,false,264⟩,⟨true,true,221⟩,⟨true,true,591⟩,⟨false,false,215⟩],.automatic),
([⟨true,false,426⟩,⟨false,false,215⟩,⟨false,false,264⟩,⟨true,false,535⟩,⟨true,true,215⟩,⟨false,false,221⟩],.automatic),
([⟨true,false,426⟩,⟨false,false,215⟩,⟨false,false,264⟩,⟨true,true,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,false,426⟩,⟨false,false,215⟩,⟨false,false,264⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,false,426⟩,⟨false,false,215⟩,⟨false,false,264⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.automatic),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.automatic),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,221⟩,⟨true,true,591⟩,⟨false,false,215⟩],.automatic),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,false,535⟩,⟨true,true,215⟩,⟨false,false,221⟩],.automatic),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,true,264⟩,⟨false,false,215⟩,⟨false,false,446⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.automatic),
([⟨true,true,264⟩,⟨false,false,215⟩,⟨false,false,446⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,264⟩,⟨false,false,215⟩,⟨false,false,446⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,264⟩,⟨false,false,215⟩,⟨false,false,446⟩,⟨true,true,221⟩,⟨true,true,591⟩,⟨false,false,215⟩],.automatic),
([⟨true,true,264⟩,⟨false,false,215⟩,⟨false,false,446⟩,⟨true,false,535⟩,⟨true,true,215⟩,⟨false,false,221⟩],.automatic),
([⟨true,true,264⟩,⟨false,false,215⟩,⟨false,false,446⟩,⟨true,true,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,264⟩,⟨false,false,215⟩,⟨false,false,446⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,264⟩,⟨false,false,215⟩,⟨false,false,446⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.automatic),
([⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨true,true,221⟩,⟨true,true,591⟩,⟨false,false,215⟩],.automatic),
([⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨true,false,535⟩,⟨true,true,215⟩,⟨false,false,221⟩],.automatic),
([⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨true,true,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,false,426⟩,⟨true,true,215⟩,⟨false,false,264⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.automatic),
([⟨true,false,426⟩,⟨true,true,215⟩,⟨false,false,264⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,false,426⟩,⟨true,true,215⟩,⟨false,false,264⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.automatic),
([⟨true,false,426⟩,⟨true,true,215⟩,⟨false,false,264⟩,⟨true,true,221⟩,⟨true,true,591⟩,⟨false,false,215⟩],.automatic),
([⟨true,false,426⟩,⟨true,true,215⟩,⟨false,false,264⟩,⟨true,false,535⟩,⟨true,true,215⟩,⟨false,false,221⟩],.automatic),
([⟨true,false,426⟩,⟨true,true,215⟩,⟨false,false,264⟩,⟨true,true,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,false,426⟩,⟨true,true,215⟩,⟨false,false,264⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,false,426⟩,⟨true,true,215⟩,⟨false,false,264⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.automatic),
([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,221⟩,⟨true,true,591⟩,⟨false,false,215⟩],.automatic),
([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,false,535⟩,⟨true,true,215⟩,⟨false,false,221⟩],.automatic),
([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.automatic),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,true,221⟩,⟨true,true,591⟩,⟨false,false,215⟩],.automatic),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,false,535⟩,⟨true,true,215⟩,⟨false,false,221⟩],.automatic),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,true,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.automatic),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,true,221⟩,⟨true,true,591⟩,⟨false,false,215⟩],.automatic),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,false,535⟩,⟨true,true,215⟩,⟨false,false,221⟩],.automatic),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,true,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic)
]

private def branches_86 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨true,false,382⟩,⟨false,false,221⟩,⟨true,false,414⟩,⟨false,false,348⟩],.bound ⟨true,false,442⟩),
([⟨true,false,382⟩,⟨false,false,221⟩,⟨false,false,348⟩,⟨false,true,414⟩],.bound ⟨true,false,385⟩),
([⟨true,false,382⟩,⟨false,false,221⟩,⟨true,true,348⟩,⟨false,false,435⟩],.bound ⟨true,false,381⟩),
([⟨true,false,382⟩,⟨false,false,221⟩,⟨true,true,348⟩,⟨true,true,435⟩],.bound ⟨true,false,436⟩),
([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,false,414⟩,⟨false,false,348⟩],.bound ⟨true,false,306⟩),
([⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨false,true,414⟩],.bound ⟨true,false,329⟩),
([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],.bound ⟨true,false,340⟩),
([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],.bound ⟨true,false,262⟩),
([⟨true,true,221⟩,⟨false,false,384⟩,⟨true,false,414⟩,⟨false,false,348⟩],.bound ⟨true,false,331⟩),
([⟨true,true,221⟩,⟨false,false,384⟩,⟨false,false,348⟩,⟨false,true,414⟩],.bound ⟨true,false,353⟩),
([⟨true,true,221⟩,⟨false,false,384⟩,⟨true,true,348⟩,⟨false,false,435⟩],.bound ⟨true,false,368⟩),
([⟨true,true,221⟩,⟨false,false,384⟩,⟨true,true,348⟩,⟨true,true,435⟩],.bound ⟨true,false,270⟩),
([⟨true,true,221⟩,⟨true,true,384⟩,⟨true,false,414⟩,⟨false,false,348⟩],.bound ⟨true,false,428⟩),
([⟨true,true,221⟩,⟨true,true,384⟩,⟨false,false,348⟩,⟨false,true,414⟩],.bound ⟨true,false,397⟩),
([⟨true,true,221⟩,⟨true,true,384⟩,⟨true,true,348⟩,⟨false,false,435⟩],.bound ⟨true,false,389⟩),
([⟨true,true,221⟩,⟨true,true,384⟩,⟨true,true,348⟩,⟨true,true,435⟩],.bound ⟨true,false,421⟩)
]

private def branches_87 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨true,false,528⟩,⟨false,false,613⟩,⟨true,false,596⟩,⟨false,false,264⟩],.bound ⟨false,false,284⟩),
([⟨true,false,528⟩,⟨false,false,613⟩,⟨false,false,264⟩,⟨false,true,596⟩],.bound ⟨false,false,244⟩),
([⟨true,false,528⟩,⟨false,false,613⟩,⟨true,true,264⟩,⟨false,false,655⟩],.bound ⟨false,false,228⟩),
([⟨true,false,528⟩,⟨false,false,613⟩,⟨true,true,264⟩,⟨true,true,655⟩],.bound ⟨false,false,256⟩),
([⟨false,false,613⟩,⟨false,true,528⟩,⟨true,false,596⟩,⟨false,false,264⟩],.bound ⟨false,false,371⟩),
([⟨false,false,613⟩,⟨false,true,528⟩,⟨false,false,264⟩,⟨false,true,596⟩],.bound ⟨false,false,722⟩),
([⟨false,false,613⟩,⟨false,true,528⟩,⟨true,true,264⟩,⟨false,false,655⟩],.bound ⟨false,false,647⟩),
([⟨false,false,613⟩,⟨false,true,528⟩,⟨true,true,264⟩,⟨true,true,655⟩],.bound ⟨false,false,281⟩),
([⟨true,true,613⟩,⟨false,false,579⟩,⟨true,false,596⟩,⟨false,false,264⟩],.bound ⟨false,false,343⟩),
([⟨true,true,613⟩,⟨false,false,579⟩,⟨false,false,264⟩,⟨false,true,596⟩],.bound ⟨false,false,720⟩),
([⟨true,true,613⟩,⟨false,false,579⟩,⟨true,true,264⟩,⟨false,false,655⟩],.bound ⟨false,false,592⟩),
([⟨true,true,613⟩,⟨false,false,579⟩,⟨true,true,264⟩,⟨true,true,655⟩],.bound ⟨false,false,349⟩),
([⟨true,true,579⟩,⟨true,true,613⟩,⟨true,false,596⟩,⟨false,false,264⟩],.bound ⟨false,false,257⟩),
([⟨true,true,579⟩,⟨true,true,613⟩,⟨false,false,264⟩,⟨false,true,596⟩],.bound ⟨false,false,99⟩),
([⟨true,true,579⟩,⟨true,true,613⟩,⟨true,true,264⟩,⟨false,false,655⟩],.bound ⟨false,false,362⟩),
([⟨true,true,579⟩,⟨true,true,613⟩,⟨true,true,264⟩,⟨true,true,655⟩],.bound ⟨false,false,242⟩)
]

private def branches_88 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.automatic),
([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.automatic),
([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.automatic),
([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.automatic),
([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic),
([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.automatic),
([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.automatic),
([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.automatic),
([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic),
([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.automatic),
([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.automatic),
([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.automatic),
([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic),
([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.automatic),
([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.automatic),
([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.automatic),
([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.automatic),
([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic)
]

private def branches_89 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨true,false,375⟩,⟨false,false,254⟩,⟨true,false,434⟩,⟨false,false,321⟩],.bound ⟨true,false,468⟩),
([⟨true,false,375⟩,⟨false,false,254⟩,⟨false,false,321⟩,⟨false,true,434⟩],.bound ⟨true,false,390⟩),
([⟨true,false,375⟩,⟨false,false,254⟩,⟨true,true,321⟩,⟨false,false,454⟩],.bound ⟨true,false,383⟩),
([⟨true,false,375⟩,⟨false,false,254⟩,⟨true,true,321⟩,⟨true,true,454⟩],.bound ⟨true,false,458⟩),
([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,false,434⟩,⟨false,false,321⟩],.bound ⟨true,false,261⟩),
([⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨false,true,434⟩],.bound ⟨true,false,285⟩),
([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],.bound ⟨true,false,307⟩),
([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],.bound ⟨true,false,206⟩),
([⟨true,true,254⟩,⟨false,false,373⟩,⟨true,false,434⟩,⟨false,false,321⟩],.bound ⟨true,false,294⟩),
([⟨true,true,254⟩,⟨false,false,373⟩,⟨false,false,321⟩,⟨false,true,434⟩],.bound ⟨true,false,332⟩),
([⟨true,true,254⟩,⟨false,false,373⟩,⟨true,true,321⟩,⟨false,false,454⟩],.bound ⟨true,false,358⟩),
([⟨true,true,254⟩,⟨false,false,373⟩,⟨true,true,321⟩,⟨true,true,454⟩],.bound ⟨true,false,214⟩),
([⟨true,true,254⟩,⟨true,true,373⟩,⟨true,false,434⟩,⟨false,false,321⟩],.bound ⟨true,false,448⟩),
([⟨true,true,254⟩,⟨true,true,373⟩,⟨false,false,321⟩,⟨false,true,434⟩],.bound ⟨true,false,407⟩),
([⟨true,true,254⟩,⟨true,true,373⟩,⟨true,true,321⟩,⟨false,false,454⟩],.bound ⟨true,false,396⟩),
([⟨true,true,254⟩,⟨true,true,373⟩,⟨true,true,321⟩,⟨true,true,454⟩],.bound ⟨true,false,441⟩)
]

private def branches_90 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨true,false,612⟩,⟨false,false,640⟩,⟨true,false,563⟩,⟨false,false,296⟩],.bound ⟨false,false,258⟩),
([⟨true,false,612⟩,⟨false,false,640⟩,⟨false,false,296⟩,⟨false,true,563⟩],.bound ⟨false,false,191⟩),
([⟨true,false,612⟩,⟨false,false,640⟩,⟨true,true,296⟩,⟨false,false,631⟩],.bound ⟨false,false,179⟩),
([⟨true,false,612⟩,⟨false,false,640⟩,⟨true,true,296⟩,⟨true,true,631⟩],.bound ⟨false,false,219⟩),
([⟨false,false,640⟩,⟨false,true,612⟩,⟨true,false,563⟩,⟨false,false,296⟩],.bound ⟨false,false,398⟩),
([⟨false,false,640⟩,⟨false,true,612⟩,⟨false,false,296⟩,⟨false,true,563⟩],.bound ⟨false,false,725⟩),
([⟨false,false,640⟩,⟨false,true,612⟩,⟨true,true,296⟩,⟨false,false,631⟩],.bound ⟨false,false,706⟩),
([⟨false,false,640⟩,⟨false,true,612⟩,⟨true,true,296⟩,⟨true,true,631⟩],.bound ⟨false,false,164⟩),
([⟨true,true,640⟩,⟨false,false,675⟩,⟨true,false,563⟩,⟨false,false,296⟩],.bound ⟨false,false,324⟩),
([⟨true,true,640⟩,⟨false,false,675⟩,⟨false,false,296⟩,⟨false,true,563⟩],.bound ⟨false,false,709⟩),
([⟨true,true,640⟩,⟨false,false,675⟩,⟨true,true,296⟩,⟨false,false,631⟩],.bound ⟨false,false,657⟩),
([⟨true,true,640⟩,⟨false,false,675⟩,⟨true,true,296⟩,⟨true,true,631⟩],.bound ⟨false,false,301⟩),
([⟨true,true,640⟩,⟨true,true,675⟩,⟨true,false,563⟩,⟨false,false,296⟩],.bound ⟨false,false,220⟩),
([⟨true,true,640⟩,⟨true,true,675⟩,⟨false,false,296⟩,⟨false,true,563⟩],.bound ⟨false,false,158⟩),
([⟨true,true,640⟩,⟨true,true,675⟩,⟨true,true,296⟩,⟨false,false,631⟩],.bound ⟨false,false,380⟩),
([⟨true,true,640⟩,⟨true,true,675⟩,⟨true,true,296⟩,⟨true,true,631⟩],.bound ⟨false,false,196⟩)
]

private def branches_91 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨true,false,601⟩,⟨false,false,629⟩,⟨false,false,634⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.automatic),
([⟨true,false,601⟩,⟨false,false,629⟩,⟨false,false,634⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.automatic),
([⟨true,false,601⟩,⟨false,false,629⟩,⟨false,false,634⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.automatic),
([⟨true,false,601⟩,⟨false,false,629⟩,⟨false,false,634⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.automatic),
([⟨true,false,601⟩,⟨false,false,629⟩,⟨false,false,634⟩,⟨true,false,516⟩,⟨true,true,629⟩,⟨false,false,223⟩],.automatic),
([⟨true,false,601⟩,⟨false,false,629⟩,⟨false,false,634⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.automatic),
([⟨true,false,601⟩,⟨false,false,629⟩,⟨false,false,634⟩,⟨true,true,223⟩,⟨true,true,629⟩,⟨false,false,569⟩],.automatic),
([⟨true,false,601⟩,⟨false,false,629⟩,⟨false,false,634⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨true,true,629⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,false,516⟩,⟨true,true,629⟩,⟨false,false,223⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,223⟩,⟨true,true,629⟩,⟨false,false,569⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨true,true,629⟩],.automatic),
([⟨true,true,634⟩,⟨false,false,629⟩,⟨false,false,664⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.automatic),
([⟨true,true,634⟩,⟨false,false,629⟩,⟨false,false,664⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.automatic),
([⟨true,true,634⟩,⟨false,false,629⟩,⟨false,false,664⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.automatic),
([⟨true,true,634⟩,⟨false,false,629⟩,⟨false,false,664⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.automatic),
([⟨true,true,634⟩,⟨false,false,629⟩,⟨false,false,664⟩,⟨true,false,516⟩,⟨true,true,629⟩,⟨false,false,223⟩],.automatic),
([⟨true,true,634⟩,⟨false,false,629⟩,⟨false,false,664⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.automatic),
([⟨true,true,634⟩,⟨false,false,629⟩,⟨false,false,664⟩,⟨true,true,223⟩,⟨true,true,629⟩,⟨false,false,569⟩],.automatic),
([⟨true,true,634⟩,⟨false,false,629⟩,⟨false,false,664⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨true,true,629⟩],.automatic),
([⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,629⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.automatic),
([⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,629⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.automatic),
([⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.automatic),
([⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.automatic),
([⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,629⟩,⟨true,false,516⟩,⟨true,true,629⟩,⟨false,false,223⟩],.automatic),
([⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,629⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.automatic),
([⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,629⟩,⟨false,false,569⟩],.automatic),
([⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,629⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨true,true,629⟩],.automatic),
([⟨true,false,601⟩,⟨true,true,629⟩,⟨false,false,634⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.automatic),
([⟨true,false,601⟩,⟨true,true,629⟩,⟨false,false,634⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.automatic),
([⟨true,false,601⟩,⟨true,true,629⟩,⟨false,false,634⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.automatic),
([⟨true,false,601⟩,⟨true,true,629⟩,⟨false,false,634⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.automatic),
([⟨true,false,601⟩,⟨true,true,629⟩,⟨false,false,634⟩,⟨true,false,516⟩,⟨true,true,629⟩,⟨false,false,223⟩],.automatic),
([⟨true,false,601⟩,⟨true,true,629⟩,⟨false,false,634⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.automatic),
([⟨true,false,601⟩,⟨true,true,629⟩,⟨false,false,634⟩,⟨true,true,223⟩,⟨true,true,629⟩,⟨false,false,569⟩],.automatic),
([⟨true,false,601⟩,⟨true,true,629⟩,⟨false,false,634⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨true,true,629⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,false,516⟩,⟨true,true,629⟩,⟨false,false,223⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,223⟩,⟨true,true,629⟩,⟨false,false,569⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨true,true,629⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,false,516⟩,⟨true,true,629⟩,⟨false,false,223⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,223⟩,⟨true,true,629⟩,⟨false,false,569⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨true,true,629⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,false,516⟩,⟨true,true,629⟩,⟨false,false,223⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,true,223⟩,⟨true,true,629⟩,⟨false,false,569⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨true,true,629⟩],.automatic)
]

private def branches_92 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨true,false,347⟩,⟨false,false,223⟩,⟨true,false,466⟩,⟨false,false,216⟩],.bound ⟨true,false,524⟩),
([⟨true,false,347⟩,⟨false,false,223⟩,⟨false,false,216⟩,⟨false,true,466⟩],.bound ⟨true,false,404⟩),
([⟨true,false,347⟩,⟨false,false,223⟩,⟨true,true,216⟩,⟨false,false,497⟩],.bound ⟨true,false,395⟩),
([⟨true,false,347⟩,⟨false,false,223⟩,⟨true,true,216⟩,⟨true,true,497⟩],.bound ⟨true,false,512⟩),
([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,false,466⟩,⟨false,false,216⟩],.bound ⟨true,false,140⟩),
([⟨false,false,223⟩,⟨false,true,347⟩,⟨false,false,216⟩,⟨false,true,466⟩],.bound ⟨true,false,186⟩),
([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨false,false,497⟩],.bound ⟨true,false,205⟩),
([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨true,true,497⟩],.bound ⟨true,false,95⟩),
([⟨true,true,223⟩,⟨false,false,328⟩,⟨true,false,466⟩,⟨false,false,216⟩],.bound ⟨true,false,218⟩),
([⟨true,true,223⟩,⟨false,false,328⟩,⟨false,false,216⟩,⟨false,true,466⟩],.bound ⟨true,false,290⟩),
([⟨true,true,223⟩,⟨false,false,328⟩,⟨true,true,216⟩,⟨false,false,497⟩],.bound ⟨true,false,335⟩),
([⟨true,true,223⟩,⟨false,false,328⟩,⟨true,true,216⟩,⟨true,true,497⟩],.bound ⟨true,false,106⟩),
([⟨true,true,223⟩,⟨true,true,328⟩,⟨true,false,466⟩,⟨false,false,216⟩],.bound ⟨true,false,499⟩),
([⟨true,true,223⟩,⟨true,true,328⟩,⟨false,false,216⟩,⟨false,true,466⟩],.bound ⟨true,false,425⟩),
([⟨true,true,223⟩,⟨true,true,328⟩,⟨true,true,216⟩,⟨false,false,497⟩],.bound ⟨true,false,412⟩),
([⟨true,true,223⟩,⟨true,true,328⟩,⟨true,true,216⟩,⟨true,true,497⟩],.bound ⟨true,false,484⟩)
]

private def branches_93 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨true,false,177⟩,⟨false,false,567⟩,⟨true,false,605⟩,⟨false,false,634⟩],.bound ⟨false,false,200⟩),
([⟨true,false,177⟩,⟨false,false,567⟩,⟨false,false,634⟩,⟨false,true,605⟩],.bound ⟨false,false,128⟩),
([⟨true,false,177⟩,⟨false,false,567⟩,⟨true,true,634⟩,⟨false,false,668⟩],.bound ⟨false,false,115⟩),
([⟨true,false,177⟩,⟨false,false,567⟩,⟨true,true,634⟩,⟨true,true,668⟩],.bound ⟨false,false,153⟩),
([⟨false,false,567⟩,⟨false,true,177⟩,⟨true,false,605⟩,⟨false,false,634⟩],.bound ⟨false,false,236⟩),
([⟨false,false,567⟩,⟨false,true,177⟩,⟨false,false,634⟩,⟨false,true,605⟩],.bound ⟨false,false,15⟩),
([⟨false,false,567⟩,⟨false,true,177⟩,⟨true,true,634⟩,⟨false,false,668⟩],.bound ⟨false,false,11⟩),
([⟨false,false,567⟩,⟨false,true,177⟩,⟨true,true,634⟩,⟨true,true,668⟩],.bound ⟨false,false,716⟩),
([⟨true,true,567⟩,⟨false,false,110⟩,⟨true,false,605⟩,⟨false,false,634⟩],.bound ⟨false,false,267⟩),
([⟨true,true,567⟩,⟨false,false,110⟩,⟨false,false,634⟩,⟨false,true,605⟩],.bound ⟨false,false,746⟩),
([⟨true,true,567⟩,⟨false,false,110⟩,⟨true,true,634⟩,⟨false,false,668⟩],.bound ⟨false,false,731⟩),
([⟨true,true,567⟩,⟨false,false,110⟩,⟨true,true,634⟩,⟨true,true,668⟩],.bound ⟨false,false,121⟩),
([⟨true,true,110⟩,⟨true,true,567⟩,⟨true,false,605⟩,⟨false,false,634⟩],.bound ⟨false,false,154⟩),
([⟨true,true,110⟩,⟨true,true,567⟩,⟨false,false,634⟩,⟨false,true,605⟩],.bound ⟨false,false,208⟩),
([⟨true,true,110⟩,⟨true,true,567⟩,⟨true,true,634⟩,⟨false,false,668⟩],.bound ⟨false,false,476⟩),
([⟨true,true,110⟩,⟨true,true,567⟩,⟨true,true,634⟩,⟨true,true,668⟩],.bound ⟨false,false,130⟩)
]

private def branches_94 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨true,false,426⟩,⟨false,false,215⟩,⟨false,false,264⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.bound ⟨true,false,523⟩),
([⟨true,false,426⟩,⟨false,false,215⟩,⟨false,false,264⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,419⟩),
([⟨true,false,426⟩,⟨false,false,215⟩,⟨false,false,264⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,365⟩),
([⟨true,false,426⟩,⟨false,false,215⟩,⟨false,false,264⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,511⟩),
([⟨true,false,426⟩,⟨false,false,215⟩,⟨false,false,264⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.bound ⟨true,false,523⟩),
([⟨true,false,426⟩,⟨false,false,215⟩,⟨false,false,264⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,419⟩),
([⟨true,false,426⟩,⟨false,false,215⟩,⟨false,false,264⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.bound ⟨true,false,365⟩),
([⟨true,false,426⟩,⟨false,false,215⟩,⟨false,false,264⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.bound ⟨true,false,511⟩),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.bound ⟨true,false,224⟩),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,185⟩),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,137⟩),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.bound ⟨true,false,224⟩),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,185⟩),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩),
([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.bound ⟨true,false,137⟩),
([⟨true,true,264⟩,⟨false,false,215⟩,⟨false,false,446⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.bound ⟨true,false,249⟩),
([⟨true,true,264⟩,⟨false,false,215⟩,⟨false,false,446⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,204⟩),
([⟨true,true,264⟩,⟨false,false,215⟩,⟨false,false,446⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,334⟩),
([⟨true,true,264⟩,⟨false,false,215⟩,⟨false,false,446⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,142⟩),
([⟨true,true,264⟩,⟨false,false,215⟩,⟨false,false,446⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.bound ⟨true,false,249⟩),
([⟨true,true,264⟩,⟨false,false,215⟩,⟨false,false,446⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,204⟩),
([⟨true,true,264⟩,⟨false,false,215⟩,⟨false,false,446⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.bound ⟨true,false,334⟩),
([⟨true,true,264⟩,⟨false,false,215⟩,⟨false,false,446⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.bound ⟨true,false,142⟩),
([⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.bound ⟨true,false,498⟩),
([⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,460⟩),
([⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,405⟩),
([⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,483⟩),
([⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.bound ⟨true,false,498⟩),
([⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,460⟩),
([⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.bound ⟨true,false,405⟩),
([⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.bound ⟨true,false,483⟩),
([⟨true,false,426⟩,⟨true,true,215⟩,⟨false,false,264⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.bound ⟨true,false,523⟩),
([⟨true,false,426⟩,⟨true,true,215⟩,⟨false,false,264⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,419⟩),
([⟨true,false,426⟩,⟨true,true,215⟩,⟨false,false,264⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,365⟩),
([⟨true,false,426⟩,⟨true,true,215⟩,⟨false,false,264⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,511⟩),
([⟨true,false,426⟩,⟨true,true,215⟩,⟨false,false,264⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.bound ⟨true,false,523⟩),
([⟨true,false,426⟩,⟨true,true,215⟩,⟨false,false,264⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,419⟩),
([⟨true,false,426⟩,⟨true,true,215⟩,⟨false,false,264⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.bound ⟨true,false,365⟩),
([⟨true,false,426⟩,⟨true,true,215⟩,⟨false,false,264⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.bound ⟨true,false,511⟩),
([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.bound ⟨true,false,224⟩),
([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,185⟩),
([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩),
([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,137⟩),
([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.bound ⟨true,false,224⟩),
([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,185⟩),
([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩),
([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.bound ⟨true,false,137⟩),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.bound ⟨true,false,249⟩),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,204⟩),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,334⟩),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,142⟩),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.bound ⟨true,false,249⟩),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,204⟩),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.bound ⟨true,false,334⟩),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.bound ⟨true,false,142⟩),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.bound ⟨true,false,498⟩),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,460⟩),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,405⟩),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,483⟩),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.bound ⟨true,false,498⟩),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,460⟩),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.bound ⟨true,false,405⟩),
([⟨true,true,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.bound ⟨true,false,483⟩)
]

private def branches_95 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.automatic),
([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.automatic),
([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,true,221⟩,⟨true,true,591⟩,⟨false,false,215⟩],.automatic),
([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,535⟩,⟨true,true,215⟩,⟨false,false,221⟩],.automatic),
([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,true,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,221⟩,⟨true,true,591⟩,⟨false,false,215⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,false,535⟩,⟨true,true,215⟩,⟨false,false,221⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.automatic),
([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨true,true,221⟩,⟨true,true,591⟩,⟨false,false,215⟩],.automatic),
([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨true,false,535⟩,⟨true,true,215⟩,⟨false,false,221⟩],.automatic),
([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨true,true,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.automatic),
([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,true,221⟩,⟨true,true,591⟩,⟨false,false,215⟩],.automatic),
([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,false,535⟩,⟨true,true,215⟩,⟨false,false,221⟩],.automatic),
([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,true,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.automatic),
([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.automatic),
([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨true,true,221⟩,⟨true,true,591⟩,⟨false,false,215⟩],.automatic),
([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨true,false,535⟩,⟨true,true,215⟩,⟨false,false,221⟩],.automatic),
([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨true,true,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,221⟩,⟨true,true,591⟩,⟨false,false,215⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,false,535⟩,⟨true,true,215⟩,⟨false,false,221⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,221⟩,⟨true,true,591⟩,⟨false,false,215⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,false,535⟩,⟨true,true,215⟩,⟨false,false,221⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,221⟩,⟨true,true,591⟩,⟨false,false,215⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,false,535⟩,⟨true,true,215⟩,⟨false,false,221⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.automatic),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.automatic)
]

private def branches_96 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.bound ⟨true,false,583⟩),
([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.bound ⟨true,false,416⟩),
([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.bound ⟨true,false,376⟩),
([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.bound ⟨true,false,561⟩),
([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,516⟩,⟨true,true,629⟩,⟨false,false,223⟩],.bound ⟨true,false,583⟩),
([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.bound ⟨true,false,416⟩),
([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,true,223⟩,⟨true,true,629⟩,⟨false,false,569⟩],.bound ⟨true,false,376⟩),
([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨true,true,629⟩],.bound ⟨true,false,561⟩),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.bound ⟨true,false,117⟩),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.bound ⟨true,false,147⟩),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.bound ⟨true,false,203⟩),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.bound ⟨true,false,70⟩),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,false,516⟩,⟨true,true,629⟩,⟨false,false,223⟩],.bound ⟨true,false,117⟩),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.bound ⟨true,false,147⟩),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨true,true,629⟩,⟨false,false,569⟩],.bound ⟨true,false,203⟩),
([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨true,true,629⟩],.bound ⟨true,false,70⟩),
([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.bound ⟨true,false,161⟩),
([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.bound ⟨true,false,202⟩),
([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.bound ⟨true,false,304⟩),
([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.bound ⟨true,false,74⟩),
([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨true,false,516⟩,⟨true,true,629⟩,⟨false,false,223⟩],.bound ⟨true,false,161⟩),
([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.bound ⟨true,false,202⟩),
([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨true,true,223⟩,⟨true,true,629⟩,⟨false,false,569⟩],.bound ⟨true,false,304⟩),
([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨true,true,629⟩],.bound ⟨true,false,74⟩),
([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.bound ⟨true,false,546⟩),
([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.bound ⟨true,false,463⟩),
([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.bound ⟨true,false,429⟩),
([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.bound ⟨true,false,530⟩),
([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,false,516⟩,⟨true,true,629⟩,⟨false,false,223⟩],.bound ⟨true,false,546⟩),
([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.bound ⟨true,false,463⟩),
([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,true,223⟩,⟨true,true,629⟩,⟨false,false,569⟩],.bound ⟨true,false,429⟩),
([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨true,true,629⟩],.bound ⟨true,false,530⟩),
([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.bound ⟨true,false,583⟩),
([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.bound ⟨true,false,416⟩),
([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.bound ⟨true,false,376⟩),
([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.bound ⟨true,false,561⟩),
([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨true,false,516⟩,⟨true,true,629⟩,⟨false,false,223⟩],.bound ⟨true,false,583⟩),
([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.bound ⟨true,false,416⟩),
([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨true,true,223⟩,⟨true,true,629⟩,⟨false,false,569⟩],.bound ⟨true,false,376⟩),
([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨true,true,629⟩],.bound ⟨true,false,561⟩),
([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.bound ⟨true,false,117⟩),
([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.bound ⟨true,false,147⟩),
([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.bound ⟨true,false,203⟩),
([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.bound ⟨true,false,70⟩),
([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,false,516⟩,⟨true,true,629⟩,⟨false,false,223⟩],.bound ⟨true,false,117⟩),
([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.bound ⟨true,false,147⟩),
([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨true,true,629⟩,⟨false,false,569⟩],.bound ⟨true,false,203⟩),
([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨true,true,629⟩],.bound ⟨true,false,70⟩),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.bound ⟨true,false,161⟩),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.bound ⟨true,false,202⟩),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.bound ⟨true,false,304⟩),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.bound ⟨true,false,74⟩),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,false,516⟩,⟨true,true,629⟩,⟨false,false,223⟩],.bound ⟨true,false,161⟩),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.bound ⟨true,false,202⟩),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,223⟩,⟨true,true,629⟩,⟨false,false,569⟩],.bound ⟨true,false,304⟩),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨true,true,629⟩],.bound ⟨true,false,74⟩),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.bound ⟨true,false,546⟩),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.bound ⟨true,false,463⟩),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.bound ⟨true,false,429⟩),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.bound ⟨true,false,530⟩),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,false,516⟩,⟨true,true,629⟩,⟨false,false,223⟩],.bound ⟨true,false,546⟩),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.bound ⟨true,false,463⟩),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,223⟩,⟨true,true,629⟩,⟨false,false,569⟩],.bound ⟨true,false,429⟩),
([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨true,true,629⟩],.bound ⟨true,false,530⟩)
]

private def branches_97 : List (List MiddleCertBoundRef × RefComparison) := [
([⟨true,false,601⟩,⟨false,false,629⟩,⟨false,false,634⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.automatic),
([⟨true,false,601⟩,⟨false,false,629⟩,⟨false,false,634⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,false,601⟩,⟨false,false,629⟩,⟨false,false,634⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.automatic),
([⟨true,false,601⟩,⟨false,false,629⟩,⟨false,false,634⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.automatic),
([⟨true,false,601⟩,⟨false,false,629⟩,⟨false,false,634⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.automatic),
([⟨true,false,601⟩,⟨false,false,629⟩,⟨false,false,634⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,false,601⟩,⟨false,false,629⟩,⟨false,false,634⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨true,false,601⟩,⟨false,false,629⟩,⟨false,false,634⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic),
([⟨true,true,634⟩,⟨false,false,629⟩,⟨false,false,664⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.automatic),
([⟨true,true,634⟩,⟨false,false,629⟩,⟨false,false,664⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,634⟩,⟨false,false,629⟩,⟨false,false,664⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,634⟩,⟨false,false,629⟩,⟨false,false,664⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.automatic),
([⟨true,true,634⟩,⟨false,false,629⟩,⟨false,false,664⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.automatic),
([⟨true,true,634⟩,⟨false,false,629⟩,⟨false,false,664⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,634⟩,⟨false,false,629⟩,⟨false,false,664⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,634⟩,⟨false,false,629⟩,⟨false,false,664⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic),
([⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,629⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.automatic),
([⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,629⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,629⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,629⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.automatic),
([⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,629⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.automatic),
([⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,629⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,629⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,629⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic),
([⟨true,false,601⟩,⟨true,true,629⟩,⟨false,false,634⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.automatic),
([⟨true,false,601⟩,⟨true,true,629⟩,⟨false,false,634⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,false,601⟩,⟨true,true,629⟩,⟨false,false,634⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.automatic),
([⟨true,false,601⟩,⟨true,true,629⟩,⟨false,false,634⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.automatic),
([⟨true,false,601⟩,⟨true,true,629⟩,⟨false,false,634⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.automatic),
([⟨true,false,601⟩,⟨true,true,629⟩,⟨false,false,634⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,false,601⟩,⟨true,true,629⟩,⟨false,false,634⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨true,false,601⟩,⟨true,true,629⟩,⟨false,false,634⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.automatic),
([⟨true,true,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.automatic)
]

private def branchTable : List (List (List MiddleCertBoundRef × RefComparison)) := [
  branches_83,
  branches_84,
  branches_85,
  branches_86,
  branches_87,
  branches_88,
  branches_89,
  branches_90,
  branches_91,
  branches_92,
  branches_93,
  branches_94,
  branches_95,
  branches_96,
  branches_97
]

private def cachedBranches (g : ℕ) : List (List MiddleCertBoundRef × RefComparison) :=
  branchTable[g - 83]?.getD []

private def parentRefs : List (List MiddleCertBoundRef) := [
  [⟨true,false,433⟩,⟨true,false,516⟩,⟨true,false,583⟩,⟨false,false,222⟩,⟨false,false,223⟩,⟨false,false,296⟩,⟨false,false,629⟩,⟨false,false,633⟩],
  [⟨true,false,416⟩,⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,223⟩,⟨false,false,296⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,516⟩],
  [⟨true,false,376⟩,⟨true,false,433⟩,⟨true,true,223⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨false,false,569⟩,⟨false,false,629⟩,⟨false,false,633⟩],
  [⟨true,false,433⟩,⟨true,false,561⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨false,false,629⟩,⟨false,false,633⟩],
  [⟨true,false,433⟩,⟨true,false,516⟩,⟨true,false,583⟩,⟨true,true,629⟩,⟨false,false,222⟩,⟨false,false,223⟩,⟨false,false,296⟩,⟨false,false,633⟩],
  [⟨true,false,416⟩,⟨true,false,433⟩,⟨true,true,629⟩,⟨false,false,222⟩,⟨false,false,223⟩,⟨false,false,296⟩,⟨false,false,633⟩,⟨false,true,516⟩],
  [⟨true,false,376⟩,⟨true,false,433⟩,⟨true,true,223⟩,⟨true,true,629⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨false,false,569⟩,⟨false,false,633⟩],
  [⟨true,false,433⟩,⟨true,false,561⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨true,true,629⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨false,false,633⟩],
  [⟨true,false,117⟩,⟨true,false,516⟩,⟨false,false,222⟩,⟨false,false,223⟩,⟨false,false,296⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,433⟩],
  [⟨true,false,147⟩,⟨false,false,222⟩,⟨false,false,223⟩,⟨false,false,296⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,433⟩,⟨false,true,516⟩],
  [⟨true,false,203⟩,⟨true,true,223⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨false,false,569⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,433⟩],
  [⟨true,false,70⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,433⟩],
  [⟨true,false,117⟩,⟨true,false,516⟩,⟨true,true,629⟩,⟨false,false,222⟩,⟨false,false,223⟩,⟨false,false,296⟩,⟨false,false,633⟩,⟨false,true,433⟩],
  [⟨true,false,147⟩,⟨true,true,629⟩,⟨false,false,222⟩,⟨false,false,223⟩,⟨false,false,296⟩,⟨false,false,633⟩,⟨false,true,433⟩,⟨false,true,516⟩],
  [⟨true,false,203⟩,⟨true,true,223⟩,⟨true,true,629⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨false,false,569⟩,⟨false,false,633⟩,⟨false,true,433⟩],
  [⟨true,false,70⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨true,true,629⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨false,false,633⟩,⟨false,true,433⟩],
  [⟨true,false,161⟩,⟨true,false,516⟩,⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,223⟩,⟨false,false,453⟩,⟨false,false,629⟩,⟨false,false,633⟩],
  [⟨true,false,202⟩,⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,223⟩,⟨false,false,453⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,516⟩],
  [⟨true,false,304⟩,⟨true,true,223⟩,⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨false,false,569⟩,⟨false,false,629⟩,⟨false,false,633⟩],
  [⟨true,false,74⟩,⟨true,true,223⟩,⟨true,true,296⟩,⟨true,true,569⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨false,false,629⟩,⟨false,false,633⟩],
  [⟨true,false,161⟩,⟨true,false,516⟩,⟨true,true,296⟩,⟨true,true,629⟩,⟨false,false,222⟩,⟨false,false,223⟩,⟨false,false,453⟩,⟨false,false,633⟩],
  [⟨true,false,202⟩,⟨true,true,296⟩,⟨true,true,629⟩,⟨false,false,222⟩,⟨false,false,223⟩,⟨false,false,453⟩,⟨false,false,633⟩,⟨false,true,516⟩],
  [⟨true,false,304⟩,⟨true,true,223⟩,⟨true,true,296⟩,⟨true,true,629⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨false,false,569⟩,⟨false,false,633⟩],
  [⟨true,false,74⟩,⟨true,true,223⟩,⟨true,true,296⟩,⟨true,true,569⟩,⟨true,true,629⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨false,false,633⟩],
  [⟨true,false,516⟩,⟨true,false,546⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,false,633⟩],
  [⟨true,false,463⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,516⟩],
  [⟨true,false,429⟩,⟨true,true,223⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨false,false,569⟩,⟨false,false,629⟩,⟨false,false,633⟩],
  [⟨true,false,530⟩,⟨true,true,223⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,569⟩,⟨false,false,222⟩,⟨false,false,629⟩,⟨false,false,633⟩],
  [⟨true,false,516⟩,⟨true,false,546⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨false,false,222⟩,⟨false,false,223⟩,⟨false,false,633⟩],
  [⟨true,false,463⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨false,false,222⟩,⟨false,false,223⟩,⟨false,false,633⟩,⟨false,true,516⟩],
  [⟨true,false,429⟩,⟨true,true,223⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨false,false,222⟩,⟨false,false,569⟩,⟨false,false,633⟩],
  [⟨true,false,530⟩,⟨true,true,223⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,569⟩,⟨true,true,629⟩,⟨false,false,222⟩,⟨false,false,633⟩],
  [⟨true,false,433⟩,⟨true,false,516⟩,⟨true,false,583⟩,⟨true,true,222⟩,⟨false,false,223⟩,⟨false,false,296⟩,⟨false,false,629⟩,⟨false,false,633⟩],
  [⟨true,false,416⟩,⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,223⟩,⟨false,false,296⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,516⟩],
  [⟨true,false,376⟩,⟨true,false,433⟩,⟨true,true,222⟩,⟨true,true,223⟩,⟨false,false,296⟩,⟨false,false,569⟩,⟨false,false,629⟩,⟨false,false,633⟩],
  [⟨true,false,433⟩,⟨true,false,561⟩,⟨true,true,222⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,296⟩,⟨false,false,629⟩,⟨false,false,633⟩],
  [⟨true,false,433⟩,⟨true,false,516⟩,⟨true,false,583⟩,⟨true,true,222⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,false,296⟩,⟨false,false,633⟩],
  [⟨true,false,416⟩,⟨true,false,433⟩,⟨true,true,222⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,false,296⟩,⟨false,false,633⟩,⟨false,true,516⟩],
  [⟨true,false,376⟩,⟨true,false,433⟩,⟨true,true,222⟩,⟨true,true,223⟩,⟨true,true,629⟩,⟨false,false,296⟩,⟨false,false,569⟩,⟨false,false,633⟩],
  [⟨true,false,433⟩,⟨true,false,561⟩,⟨true,true,222⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨true,true,629⟩,⟨false,false,296⟩,⟨false,false,633⟩],
  [⟨true,false,117⟩,⟨true,false,516⟩,⟨true,true,222⟩,⟨false,false,223⟩,⟨false,false,296⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,433⟩],
  [⟨true,false,147⟩,⟨true,true,222⟩,⟨false,false,223⟩,⟨false,false,296⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,433⟩,⟨false,true,516⟩],
  [⟨true,false,203⟩,⟨true,true,222⟩,⟨true,true,223⟩,⟨false,false,296⟩,⟨false,false,569⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,433⟩],
  [⟨true,false,70⟩,⟨true,true,222⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,296⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,433⟩],
  [⟨true,false,117⟩,⟨true,false,516⟩,⟨true,true,222⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,false,296⟩,⟨false,false,633⟩,⟨false,true,433⟩],
  [⟨true,false,147⟩,⟨true,true,222⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,false,296⟩,⟨false,false,633⟩,⟨false,true,433⟩,⟨false,true,516⟩],
  [⟨true,false,203⟩,⟨true,true,222⟩,⟨true,true,223⟩,⟨true,true,629⟩,⟨false,false,296⟩,⟨false,false,569⟩,⟨false,false,633⟩,⟨false,true,433⟩],
  [⟨true,false,70⟩,⟨true,true,222⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨true,true,629⟩,⟨false,false,296⟩,⟨false,false,633⟩,⟨false,true,433⟩],
  [⟨true,false,161⟩,⟨true,false,516⟩,⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,223⟩,⟨false,false,453⟩,⟨false,false,629⟩,⟨false,false,633⟩],
  [⟨true,false,202⟩,⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,223⟩,⟨false,false,453⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,516⟩],
  [⟨true,false,304⟩,⟨true,true,222⟩,⟨true,true,223⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨false,false,569⟩,⟨false,false,629⟩,⟨false,false,633⟩],
  [⟨true,false,74⟩,⟨true,true,222⟩,⟨true,true,223⟩,⟨true,true,296⟩,⟨true,true,569⟩,⟨false,false,453⟩,⟨false,false,629⟩,⟨false,false,633⟩],
  [⟨true,false,161⟩,⟨true,false,516⟩,⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,false,453⟩,⟨false,false,633⟩],
  [⟨true,false,202⟩,⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,false,453⟩,⟨false,false,633⟩,⟨false,true,516⟩],
  [⟨true,false,304⟩,⟨true,true,222⟩,⟨true,true,223⟩,⟨true,true,296⟩,⟨true,true,629⟩,⟨false,false,453⟩,⟨false,false,569⟩,⟨false,false,633⟩],
  [⟨true,false,74⟩,⟨true,true,222⟩,⟨true,true,223⟩,⟨true,true,296⟩,⟨true,true,569⟩,⟨true,true,629⟩,⟨false,false,453⟩,⟨false,false,633⟩],
  [⟨true,false,516⟩,⟨true,false,546⟩,⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,false,633⟩],
  [⟨true,false,463⟩,⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,516⟩],
  [⟨true,false,429⟩,⟨true,true,222⟩,⟨true,true,223⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,569⟩,⟨false,false,629⟩,⟨false,false,633⟩],
  [⟨true,false,530⟩,⟨true,true,222⟩,⟨true,true,223⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,569⟩,⟨false,false,629⟩,⟨false,false,633⟩],
  [⟨true,false,516⟩,⟨true,false,546⟩,⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,false,633⟩],
  [⟨true,false,463⟩,⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,false,633⟩,⟨false,true,516⟩],
  [⟨true,false,429⟩,⟨true,true,222⟩,⟨true,true,223⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨false,false,569⟩,⟨false,false,633⟩],
  [⟨true,false,530⟩,⟨true,true,222⟩,⟨true,true,223⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,569⟩,⟨true,true,629⟩,⟨false,false,633⟩],
  [⟨true,false,177⟩,⟨true,false,697⟩,⟨true,true,633⟩,⟨false,false,48⟩,⟨false,false,567⟩,⟨false,false,681⟩,⟨false,false,695⟩,⟨false,false,696⟩],
  [⟨true,false,177⟩,⟨true,true,633⟩,⟨false,false,314⟩,⟨false,false,567⟩,⟨false,false,681⟩,⟨false,false,695⟩,⟨false,false,696⟩,⟨false,true,697⟩],
  [⟨true,false,177⟩,⟨true,true,633⟩,⟨true,true,696⟩,⟨false,false,213⟩,⟨false,false,567⟩,⟨false,false,681⟩,⟨false,false,695⟩,⟨false,false,723⟩],
  [⟨true,false,177⟩,⟨true,true,633⟩,⟨true,true,696⟩,⟨true,true,723⟩,⟨false,false,34⟩,⟨false,false,567⟩,⟨false,false,681⟩,⟨false,false,695⟩],
  [⟨true,false,177⟩,⟨true,false,697⟩,⟨true,true,633⟩,⟨true,true,681⟩,⟨false,false,48⟩,⟨false,false,567⟩,⟨false,false,695⟩,⟨false,false,696⟩],
  [⟨true,false,177⟩,⟨true,true,633⟩,⟨true,true,681⟩,⟨false,false,314⟩,⟨false,false,567⟩,⟨false,false,695⟩,⟨false,false,696⟩,⟨false,true,697⟩],
  [⟨true,false,177⟩,⟨true,true,633⟩,⟨true,true,681⟩,⟨true,true,696⟩,⟨false,false,213⟩,⟨false,false,567⟩,⟨false,false,695⟩,⟨false,false,723⟩],
  [⟨true,false,177⟩,⟨true,true,633⟩,⟨true,true,681⟩,⟨true,true,696⟩,⟨true,true,723⟩,⟨false,false,34⟩,⟨false,false,567⟩,⟨false,false,695⟩],
  [⟨true,false,697⟩,⟨true,true,633⟩,⟨false,false,17⟩,⟨false,false,567⟩,⟨false,false,681⟩,⟨false,false,695⟩,⟨false,false,696⟩,⟨false,true,177⟩],
  [⟨true,true,633⟩,⟨false,false,31⟩,⟨false,false,567⟩,⟨false,false,681⟩,⟨false,false,695⟩,⟨false,false,696⟩,⟨false,true,177⟩,⟨false,true,697⟩],
  [⟨true,true,633⟩,⟨true,true,696⟩,⟨false,false,21⟩,⟨false,false,567⟩,⟨false,false,681⟩,⟨false,false,695⟩,⟨false,false,723⟩,⟨false,true,177⟩],
  [⟨true,true,633⟩,⟨true,true,696⟩,⟨true,true,723⟩,⟨false,false,567⟩,⟨false,false,681⟩,⟨false,false,695⟩,⟨false,false,718⟩,⟨false,true,177⟩],
  [⟨true,false,697⟩,⟨true,true,633⟩,⟨true,true,681⟩,⟨false,false,17⟩,⟨false,false,567⟩,⟨false,false,695⟩,⟨false,false,696⟩,⟨false,true,177⟩],
  [⟨true,true,633⟩,⟨true,true,681⟩,⟨false,false,31⟩,⟨false,false,567⟩,⟨false,false,695⟩,⟨false,false,696⟩,⟨false,true,177⟩,⟨false,true,697⟩],
  [⟨true,true,633⟩,⟨true,true,681⟩,⟨true,true,696⟩,⟨false,false,21⟩,⟨false,false,567⟩,⟨false,false,695⟩,⟨false,false,723⟩,⟨false,true,177⟩],
  [⟨true,true,633⟩,⟨true,true,681⟩,⟨true,true,696⟩,⟨true,true,723⟩,⟨false,false,567⟩,⟨false,false,695⟩,⟨false,false,718⟩,⟨false,true,177⟩],
  [⟨true,false,697⟩,⟨true,true,567⟩,⟨true,true,633⟩,⟨false,false,19⟩,⟨false,false,110⟩,⟨false,false,681⟩,⟨false,false,695⟩,⟨false,false,696⟩],
  [⟨true,true,567⟩,⟨true,true,633⟩,⟨false,false,110⟩,⟨false,false,681⟩,⟨false,false,695⟩,⟨false,false,696⟩,⟨false,false,762⟩,⟨false,true,697⟩],
  [⟨true,true,567⟩,⟨true,true,633⟩,⟨true,true,696⟩,⟨false,false,110⟩,⟨false,false,681⟩,⟨false,false,695⟩,⟨false,false,723⟩,⟨false,false,753⟩],
  [⟨true,true,567⟩,⟨true,true,633⟩,⟨true,true,696⟩,⟨true,true,723⟩,⟨false,false,110⟩,⟨false,false,123⟩,⟨false,false,681⟩,⟨false,false,695⟩],
  [⟨true,false,697⟩,⟨true,true,567⟩,⟨true,true,633⟩,⟨true,true,681⟩,⟨false,false,19⟩,⟨false,false,110⟩,⟨false,false,695⟩,⟨false,false,696⟩],
  [⟨true,true,567⟩,⟨true,true,633⟩,⟨true,true,681⟩,⟨false,false,110⟩,⟨false,false,695⟩,⟨false,false,696⟩,⟨false,false,762⟩,⟨false,true,697⟩],
  [⟨true,true,567⟩,⟨true,true,633⟩,⟨true,true,681⟩,⟨true,true,696⟩,⟨false,false,110⟩,⟨false,false,695⟩,⟨false,false,723⟩,⟨false,false,753⟩],
  [⟨true,true,567⟩,⟨true,true,633⟩,⟨true,true,681⟩,⟨true,true,696⟩,⟨true,true,723⟩,⟨false,false,110⟩,⟨false,false,123⟩,⟨false,false,695⟩],
  [⟨true,false,697⟩,⟨true,true,110⟩,⟨true,true,567⟩,⟨true,true,633⟩,⟨false,false,35⟩,⟨false,false,681⟩,⟨false,false,695⟩,⟨false,false,696⟩],
  [⟨true,true,110⟩,⟨true,true,567⟩,⟨true,true,633⟩,⟨false,false,239⟩,⟨false,false,681⟩,⟨false,false,695⟩,⟨false,false,696⟩,⟨false,true,697⟩],
  [⟨true,true,110⟩,⟨true,true,567⟩,⟨true,true,633⟩,⟨true,true,696⟩,⟨false,false,438⟩,⟨false,false,681⟩,⟨false,false,695⟩,⟨false,false,723⟩],
  [⟨true,true,110⟩,⟨true,true,567⟩,⟨true,true,633⟩,⟨true,true,696⟩,⟨true,true,723⟩,⟨false,false,24⟩,⟨false,false,681⟩,⟨false,false,695⟩],
  [⟨true,false,697⟩,⟨true,true,110⟩,⟨true,true,567⟩,⟨true,true,633⟩,⟨true,true,681⟩,⟨false,false,35⟩,⟨false,false,695⟩,⟨false,false,696⟩],
  [⟨true,true,110⟩,⟨true,true,567⟩,⟨true,true,633⟩,⟨true,true,681⟩,⟨false,false,239⟩,⟨false,false,695⟩,⟨false,false,696⟩,⟨false,true,697⟩],
  [⟨true,true,110⟩,⟨true,true,567⟩,⟨true,true,633⟩,⟨true,true,681⟩,⟨true,true,696⟩,⟨false,false,438⟩,⟨false,false,695⟩,⟨false,false,723⟩],
  [⟨true,true,110⟩,⟨true,true,567⟩,⟨true,true,633⟩,⟨true,true,681⟩,⟨true,true,696⟩,⟨true,true,723⟩,⟨false,false,24⟩,⟨false,false,695⟩],
  [⟨true,false,177⟩,⟨true,false,697⟩,⟨true,true,633⟩,⟨true,true,695⟩,⟨false,false,48⟩,⟨false,false,567⟩,⟨false,false,681⟩,⟨false,false,696⟩],
  [⟨true,false,177⟩,⟨true,true,633⟩,⟨true,true,695⟩,⟨false,false,314⟩,⟨false,false,567⟩,⟨false,false,681⟩,⟨false,false,696⟩,⟨false,true,697⟩],
  [⟨true,false,177⟩,⟨true,true,633⟩,⟨true,true,695⟩,⟨true,true,696⟩,⟨false,false,213⟩,⟨false,false,567⟩,⟨false,false,681⟩,⟨false,false,723⟩],
  [⟨true,false,177⟩,⟨true,true,633⟩,⟨true,true,695⟩,⟨true,true,696⟩,⟨true,true,723⟩,⟨false,false,34⟩,⟨false,false,567⟩,⟨false,false,681⟩],
  [⟨true,false,177⟩,⟨true,false,697⟩,⟨true,true,633⟩,⟨true,true,681⟩,⟨true,true,695⟩,⟨false,false,48⟩,⟨false,false,567⟩,⟨false,false,696⟩],
  [⟨true,false,177⟩,⟨true,true,633⟩,⟨true,true,681⟩,⟨true,true,695⟩,⟨false,false,314⟩,⟨false,false,567⟩,⟨false,false,696⟩,⟨false,true,697⟩],
  [⟨true,false,177⟩,⟨true,true,633⟩,⟨true,true,681⟩,⟨true,true,695⟩,⟨true,true,696⟩,⟨false,false,213⟩,⟨false,false,567⟩,⟨false,false,723⟩],
  [⟨true,false,177⟩,⟨true,true,633⟩,⟨true,true,681⟩,⟨true,true,695⟩,⟨true,true,696⟩,⟨true,true,723⟩,⟨false,false,34⟩,⟨false,false,567⟩],
  [⟨true,false,697⟩,⟨true,true,633⟩,⟨true,true,695⟩,⟨false,false,17⟩,⟨false,false,567⟩,⟨false,false,681⟩,⟨false,false,696⟩,⟨false,true,177⟩],
  [⟨true,true,633⟩,⟨true,true,695⟩,⟨false,false,31⟩,⟨false,false,567⟩,⟨false,false,681⟩,⟨false,false,696⟩,⟨false,true,177⟩,⟨false,true,697⟩],
  [⟨true,true,633⟩,⟨true,true,695⟩,⟨true,true,696⟩,⟨false,false,21⟩,⟨false,false,567⟩,⟨false,false,681⟩,⟨false,false,723⟩,⟨false,true,177⟩],
  [⟨true,true,633⟩,⟨true,true,695⟩,⟨true,true,696⟩,⟨true,true,723⟩,⟨false,false,567⟩,⟨false,false,681⟩,⟨false,false,718⟩,⟨false,true,177⟩],
  [⟨true,false,697⟩,⟨true,true,633⟩,⟨true,true,681⟩,⟨true,true,695⟩,⟨false,false,17⟩,⟨false,false,567⟩,⟨false,false,696⟩,⟨false,true,177⟩],
  [⟨true,true,633⟩,⟨true,true,681⟩,⟨true,true,695⟩,⟨false,false,31⟩,⟨false,false,567⟩,⟨false,false,696⟩,⟨false,true,177⟩,⟨false,true,697⟩],
  [⟨true,true,633⟩,⟨true,true,681⟩,⟨true,true,695⟩,⟨true,true,696⟩,⟨false,false,21⟩,⟨false,false,567⟩,⟨false,false,723⟩,⟨false,true,177⟩],
  [⟨true,true,633⟩,⟨true,true,681⟩,⟨true,true,695⟩,⟨true,true,696⟩,⟨true,true,723⟩,⟨false,false,567⟩,⟨false,false,718⟩,⟨false,true,177⟩],
  [⟨true,false,697⟩,⟨true,true,567⟩,⟨true,true,633⟩,⟨true,true,695⟩,⟨false,false,19⟩,⟨false,false,110⟩,⟨false,false,681⟩,⟨false,false,696⟩],
  [⟨true,true,567⟩,⟨true,true,633⟩,⟨true,true,695⟩,⟨false,false,110⟩,⟨false,false,681⟩,⟨false,false,696⟩,⟨false,false,762⟩,⟨false,true,697⟩],
  [⟨true,true,567⟩,⟨true,true,633⟩,⟨true,true,695⟩,⟨true,true,696⟩,⟨false,false,110⟩,⟨false,false,681⟩,⟨false,false,723⟩,⟨false,false,753⟩],
  [⟨true,true,567⟩,⟨true,true,633⟩,⟨true,true,695⟩,⟨true,true,696⟩,⟨true,true,723⟩,⟨false,false,110⟩,⟨false,false,123⟩,⟨false,false,681⟩],
  [⟨true,false,697⟩,⟨true,true,567⟩,⟨true,true,633⟩,⟨true,true,681⟩,⟨true,true,695⟩,⟨false,false,19⟩,⟨false,false,110⟩,⟨false,false,696⟩],
  [⟨true,true,567⟩,⟨true,true,633⟩,⟨true,true,681⟩,⟨true,true,695⟩,⟨false,false,110⟩,⟨false,false,696⟩,⟨false,false,762⟩,⟨false,true,697⟩],
  [⟨true,true,567⟩,⟨true,true,633⟩,⟨true,true,681⟩,⟨true,true,695⟩,⟨true,true,696⟩,⟨false,false,110⟩,⟨false,false,723⟩,⟨false,false,753⟩],
  [⟨true,true,567⟩,⟨true,true,633⟩,⟨true,true,681⟩,⟨true,true,695⟩,⟨true,true,696⟩,⟨true,true,723⟩,⟨false,false,110⟩,⟨false,false,123⟩],
  [⟨true,false,697⟩,⟨true,true,110⟩,⟨true,true,567⟩,⟨true,true,633⟩,⟨true,true,695⟩,⟨false,false,35⟩,⟨false,false,681⟩,⟨false,false,696⟩],
  [⟨true,true,110⟩,⟨true,true,567⟩,⟨true,true,633⟩,⟨true,true,695⟩,⟨false,false,239⟩,⟨false,false,681⟩,⟨false,false,696⟩,⟨false,true,697⟩],
  [⟨true,true,110⟩,⟨true,true,567⟩,⟨true,true,633⟩,⟨true,true,695⟩,⟨true,true,696⟩,⟨false,false,438⟩,⟨false,false,681⟩,⟨false,false,723⟩],
  [⟨true,true,110⟩,⟨true,true,567⟩,⟨true,true,633⟩,⟨true,true,695⟩,⟨true,true,696⟩,⟨true,true,723⟩,⟨false,false,24⟩,⟨false,false,681⟩],
  [⟨true,false,697⟩,⟨true,true,110⟩,⟨true,true,567⟩,⟨true,true,633⟩,⟨true,true,681⟩,⟨true,true,695⟩,⟨false,false,35⟩,⟨false,false,696⟩],
  [⟨true,true,110⟩,⟨true,true,567⟩,⟨true,true,633⟩,⟨true,true,681⟩,⟨true,true,695⟩,⟨false,false,239⟩,⟨false,false,696⟩,⟨false,true,697⟩],
  [⟨true,true,110⟩,⟨true,true,567⟩,⟨true,true,633⟩,⟨true,true,681⟩,⟨true,true,695⟩,⟨true,true,696⟩,⟨false,false,438⟩,⟨false,false,723⟩],
  [⟨true,true,110⟩,⟨true,true,567⟩,⟨true,true,633⟩,⟨true,true,681⟩,⟨true,true,695⟩,⟨true,true,696⟩,⟨true,true,723⟩,⟨false,false,24⟩]
]

private def hypTable : List (List MiddleCertBoundRef) := [
  [⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],
  [⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],
  [⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],
  [⟨false,false,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],
  [⟨true,true,215⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],
  [⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],
  [⟨false,false,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],
  [⟨true,true,222⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],
  [⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],
  [⟨false,false,576⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,534⟩],
  [⟨true,true,629⟩,⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],
  [⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],
  [⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],
  [⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩],
  [⟨false,false,576⟩,⟨false,false,633⟩,⟨false,true,534⟩]
]

private def cachedHyp (g : ℕ) : List MiddleCertBoundRef :=
  hypTable[g - 83]?.getD []

private theorem hyp_83 :
    (middleCertGoal middleCertData 83).hypotheses = cachedHyp 83 := by
  decide +kernel

private theorem par_83 :
    middleCertData.parents (middleCertParity (middleCertGoal middleCertData 83).family) = parentRefs := by
  decide +kernel

private theorem hyp_84 :
    (middleCertGoal middleCertData 84).hypotheses = cachedHyp 84 := by
  decide +kernel

private theorem par_84 :
    middleCertData.parents (middleCertParity (middleCertGoal middleCertData 84).family) = parentRefs := by
  decide +kernel

private theorem hyp_85 :
    (middleCertGoal middleCertData 85).hypotheses = cachedHyp 85 := by
  decide +kernel

private theorem par_85 :
    middleCertData.parents (middleCertParity (middleCertGoal middleCertData 85).family) = parentRefs := by
  decide +kernel

private theorem hyp_86 :
    (middleCertGoal middleCertData 86).hypotheses = cachedHyp 86 := by
  decide +kernel

private theorem par_86 :
    middleCertData.parents (middleCertParity (middleCertGoal middleCertData 86).family) = parentRefs := by
  decide +kernel

private theorem hyp_87 :
    (middleCertGoal middleCertData 87).hypotheses = cachedHyp 87 := by
  decide +kernel

private theorem par_87 :
    middleCertData.parents (middleCertParity (middleCertGoal middleCertData 87).family) = parentRefs := by
  decide +kernel

private theorem hyp_88 :
    (middleCertGoal middleCertData 88).hypotheses = cachedHyp 88 := by
  decide +kernel

private theorem par_88 :
    middleCertData.parents (middleCertParity (middleCertGoal middleCertData 88).family) = parentRefs := by
  decide +kernel

private theorem hyp_89 :
    (middleCertGoal middleCertData 89).hypotheses = cachedHyp 89 := by
  decide +kernel

private theorem par_89 :
    middleCertData.parents (middleCertParity (middleCertGoal middleCertData 89).family) = parentRefs := by
  decide +kernel

private theorem hyp_90 :
    (middleCertGoal middleCertData 90).hypotheses = cachedHyp 90 := by
  decide +kernel

private theorem par_90 :
    middleCertData.parents (middleCertParity (middleCertGoal middleCertData 90).family) = parentRefs := by
  decide +kernel

private theorem hyp_91 :
    (middleCertGoal middleCertData 91).hypotheses = cachedHyp 91 := by
  decide +kernel

private theorem par_91 :
    middleCertData.parents (middleCertParity (middleCertGoal middleCertData 91).family) = parentRefs := by
  decide +kernel

private theorem hyp_92 :
    (middleCertGoal middleCertData 92).hypotheses = cachedHyp 92 := by
  decide +kernel

private theorem par_92 :
    middleCertData.parents (middleCertParity (middleCertGoal middleCertData 92).family) = parentRefs := by
  decide +kernel

private theorem hyp_93 :
    (middleCertGoal middleCertData 93).hypotheses = cachedHyp 93 := by
  decide +kernel

private theorem par_93 :
    middleCertData.parents (middleCertParity (middleCertGoal middleCertData 93).family) = parentRefs := by
  decide +kernel

private theorem hyp_94 :
    (middleCertGoal middleCertData 94).hypotheses = cachedHyp 94 := by
  decide +kernel

private theorem par_94 :
    middleCertData.parents (middleCertParity (middleCertGoal middleCertData 94).family) = parentRefs := by
  decide +kernel

private theorem hyp_95 :
    (middleCertGoal middleCertData 95).hypotheses = cachedHyp 95 := by
  decide +kernel

private theorem par_95 :
    middleCertData.parents (middleCertParity (middleCertGoal middleCertData 95).family) = parentRefs := by
  decide +kernel

private theorem hyp_96 :
    (middleCertGoal middleCertData 96).hypotheses = cachedHyp 96 := by
  decide +kernel

private theorem par_96 :
    middleCertData.parents (middleCertParity (middleCertGoal middleCertData 96).family) = parentRefs := by
  decide +kernel

private theorem hyp_97 :
    (middleCertGoal middleCertData 97).hypotheses = cachedHyp 97 := by
  decide +kernel

private theorem par_97 :
    middleCertData.parents (middleCertParity (middleCertGoal middleCertData 97).family) = parentRefs := by
  decide +kernel

private theorem cached_83 :
    middleCertGoalBranches middleCertData (middleCertGoal middleCertData 83)
      = (cachedBranches 83).map decodeBranch := by
  decide +kernel

private theorem cached_84 :
    middleCertGoalBranches middleCertData (middleCertGoal middleCertData 84)
      = (cachedBranches 84).map decodeBranch := by
  decide +kernel

private theorem cached_85 :
    middleCertGoalBranches middleCertData (middleCertGoal middleCertData 85)
      = (cachedBranches 85).map decodeBranch := by
  decide +kernel

private theorem cached_86 :
    middleCertGoalBranches middleCertData (middleCertGoal middleCertData 86)
      = (cachedBranches 86).map decodeBranch := by
  decide +kernel

private theorem cached_87 :
    middleCertGoalBranches middleCertData (middleCertGoal middleCertData 87)
      = (cachedBranches 87).map decodeBranch := by
  decide +kernel

private theorem cached_88 :
    middleCertGoalBranches middleCertData (middleCertGoal middleCertData 88)
      = (cachedBranches 88).map decodeBranch := by
  decide +kernel

private theorem cached_89 :
    middleCertGoalBranches middleCertData (middleCertGoal middleCertData 89)
      = (cachedBranches 89).map decodeBranch := by
  decide +kernel

private theorem cached_90 :
    middleCertGoalBranches middleCertData (middleCertGoal middleCertData 90)
      = (cachedBranches 90).map decodeBranch := by
  decide +kernel

private theorem cached_91 :
    middleCertGoalBranches middleCertData (middleCertGoal middleCertData 91)
      = (cachedBranches 91).map decodeBranch := by
  decide +kernel

private theorem cached_92 :
    middleCertGoalBranches middleCertData (middleCertGoal middleCertData 92)
      = (cachedBranches 92).map decodeBranch := by
  decide +kernel

private theorem cached_93 :
    middleCertGoalBranches middleCertData (middleCertGoal middleCertData 93)
      = (cachedBranches 93).map decodeBranch := by
  decide +kernel

private theorem cached_94 :
    middleCertGoalBranches middleCertData (middleCertGoal middleCertData 94)
      = (cachedBranches 94).map decodeBranch := by
  decide +kernel

private theorem cached_95 :
    middleCertGoalBranches middleCertData (middleCertGoal middleCertData 95)
      = (cachedBranches 95).map decodeBranch := by
  decide +kernel

private theorem cached_96 :
    middleCertGoalBranches middleCertData (middleCertGoal middleCertData 96)
      = (cachedBranches 96).map decodeBranch := by
  decide +kernel

private theorem cached_97 :
    middleCertGoalBranches middleCertData (middleCertGoal middleCertData 97)
      = (cachedBranches 97).map decodeBranch := by
  decide +kernel

private def goalIds : List ℕ := [83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97]

private theorem cached_ok : ∀ g ∈ goalIds,
    middleCertGoalBranches middleCertData (middleCertGoal middleCertData g)
      = (cachedBranches g).map decodeBranch := by
  simp only [goalIds, List.forall_mem_cons, List.forall_mem_nil, and_true]
  exact ⟨cached_83, cached_84, cached_85, cached_86, cached_87, cached_88, cached_89, cached_90, cached_91, cached_92, cached_93, cached_94, cached_95, cached_96, cached_97, List.forall_mem_nil _⟩

private theorem hyp_ok : ∀ g ∈ goalIds,
    (middleCertGoal middleCertData g).hypotheses = cachedHyp g := by
  simp only [goalIds, List.forall_mem_cons, List.forall_mem_nil, and_true]
  exact ⟨hyp_83, hyp_84, hyp_85, hyp_86, hyp_87, hyp_88, hyp_89, hyp_90, hyp_91, hyp_92, hyp_93, hyp_94, hyp_95, hyp_96, hyp_97, List.forall_mem_nil _⟩

private theorem par_ok : ∀ g ∈ goalIds,
    middleCertData.parents (middleCertParity (middleCertGoal middleCertData g).family) = parentRefs := by
  simp only [goalIds, List.forall_mem_cons, List.forall_mem_nil, and_true]
  exact ⟨par_83, par_84, par_85, par_86, par_87, par_88, par_89, par_90, par_91, par_92, par_93, par_94, par_95, par_96, par_97, List.forall_mem_nil _⟩

private def refBranch (g j : ℕ) : List MiddleCertBoundRef × RefComparison :=
  (cachedBranches g)[j]?.getD ([], RefComparison.impossible)

private theorem branch_decode (g j : ℕ)
    (h : middleCertGoalBranches middleCertData (middleCertGoal middleCertData g)
        = (cachedBranches g).map decodeBranch) :
    middleCertBranch middleCertData (middleCertGoal middleCertData g) j
      = decodeBranch (refBranch g j) := by
  unfold middleCertBranch refBranch
  rw [h, List.getElem?_map]
  cases (cachedBranches g)[j]? with
  | none => rfl
  | some x => rfl

private theorem branch_len (g : ℕ)
    (h : middleCertGoalBranches middleCertData (middleCertGoal middleCertData g)
        = (cachedBranches g).map decodeBranch) :
    (middleCertGoalBranches middleCertData (middleCertGoal middleCertData g)).length
      = (cachedBranches g).length := by
  rw [h, List.length_map]

private def parentSlice (parent : ℤ) : List MiddleCertBoundRef :=
  if parent < 0 then [] else parentRefs[parent.toNat]?.getD []

private def refConditions (hyp : List MiddleCertBoundRef)
    (br : List MiddleCertBoundRef × RefComparison) (parent : ℤ) : List MiddleCertBoundRef :=
  hyp ++ br.1 ++ parentSlice parent ++
    (match br.2 with | .bound b => [refComplement b] | _ => [])

/-- The part of the premise list that does not depend on the parent index. -/
private def fixedConds (hyp : List MiddleCertBoundRef)
    (br : List MiddleCertBoundRef × RefComparison) : List MiddleCertBoundRef :=
  hyp ++ br.1 ++ (match br.2 with | .bound b => [refComplement b] | _ => [])

private theorem mem_conditions (hyp : List MiddleCertBoundRef)
    (br : List MiddleCertBoundRef × RefComparison) (parent : ℤ) (a : MiddleCertBoundRef)
    (h : a ∈ fixedConds hyp br ∨ a ∈ parentSlice parent) : a ∈ refConditions hyp br parent := by
  simp only [fixedConds, refConditions, List.mem_append] at h ⊢
  tauto

private theorem conditions_eq (r : MiddleCertRecord) (hyp : List MiddleCertBoundRef) (parent : ℤ)
    (hb : middleCertGoalBranches middleCertData (middleCertGoal middleCertData r.goal)
        = (cachedBranches r.goal).map decodeBranch)
    (hh : (middleCertGoal middleCertData r.goal).hypotheses = hyp)
    (hps : middleCertData.parents
        (middleCertParity (middleCertGoal middleCertData r.goal).family) = parentRefs) :
    middleCertRecordConditions middleCertData r parent
      = middleCertBounds middleCertData (refConditions hyp (refBranch r.goal r.branch) parent) := by
  simp only [middleCertRecordConditions, refConditions,
    branch_decode r.goal r.branch hb, hh, hps, middleCertBounds, List.map_append, decodeBranch]
  by_cases hpar : parent < 0 <;>
    cases hv : (refBranch r.goal r.branch).2 <;>
      simp [hpar, hv, parentSlice, decodeComparison, refComplement, middleCertBound,
        lowerHistoryComplement]

private def recordReady (r : MiddleCertRecord) (hyp : List MiddleCertBoundRef)
    (br : List MiddleCertBoundRef × RefComparison) : Prop :=
  0 < r.goal ∧ r.goal ≤ middleCertData.goals.length ∧
  0 < r.proof ∧ r.proof ≤ middleCertData.proofs.length ∧
  r.branch < (cachedBranches r.goal).length ∧
  br.2 ≠ RefComparison.automatic ∧
  middleCertProofValid middleCertData (middleCertProof middleCertData r.proof) ∧
  (∀ parent ∈ r.parents, parent = -1 ∨ (0 ≤ parent ∧ parent.toNat < parentRefs.length)) ∧
  ∀ p ∈ middleCertProofPairs (middleCertProof middleCertData r.proof),
    (p.lowerBound ∈ fixedConds hyp br ∨ ∀ parent ∈ r.parents, p.lowerBound ∈ parentSlice parent) ∧
    (p.upperBound ∈ fixedConds hyp br ∨ ∀ parent ∈ r.parents, p.upperBound ∈ parentSlice parent)

private instance (r : MiddleCertRecord) (hyp : List MiddleCertBoundRef)
    (br : List MiddleCertBoundRef × RefComparison) : Decidable (recordReady r hyp br) := by
  unfold recordReady
  infer_instance

private theorem ready_valid (r : MiddleCertRecord) (hyp : List MiddleCertBoundRef)
    (br : List MiddleCertBoundRef × RefComparison)
    (hbr : refBranch r.goal r.branch = br)
    (hb : middleCertGoalBranches middleCertData (middleCertGoal middleCertData r.goal)
        = (cachedBranches r.goal).map decodeBranch)
    (hh : (middleCertGoal middleCertData r.goal).hypotheses = hyp)
    (hps : middleCertData.parents
        (middleCertParity (middleCertGoal middleCertData r.goal).family) = parentRefs)
    (hr : recordReady r hyp br) : middleCertRecordValid middleCertData r := by
  subst hbr
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hr
  refine ⟨h1, h2, h3, h4, ?_, ?_, h7, ?_⟩
  · rw [branch_len r.goal hb]; exact h5
  · rw [branch_decode r.goal r.branch hb]
    intro hc
    exact h6 (decode_auto hc)
  · intro parent hp
    refine ⟨?_, ?_⟩
    · rw [hps]; exact h8 parent hp
    · intro p hpp
      obtain ⟨hl, hu⟩ := h9 p hpp
      rw [conditions_eq r hyp parent hb hh hps]
      refine ⟨List.mem_map.mpr ⟨p.lowerBound, ?_, rfl⟩, List.mem_map.mpr ⟨p.upperBound, ?_, rfl⟩⟩
      · exact mem_conditions _ _ _ _ (hl.imp id (fun h => h parent hp))
      · exact mem_conditions _ _ _ _ (hu.imp id (fun h => h parent hp))

private def branchRecords_82 : List (List MiddleCertRecord) := [
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [⟨83,8,[10,42],29⟩, ⟨83,8,[9,41],51⟩, ⟨83,8,[2,34],107⟩, ⟨83,8,[8,40],149⟩, ⟨83,8,[0,32],184⟩, ⟨83,8,[1,3,33,35],503⟩, ⟨83,8,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],541⟩, ⟨83,8,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨83,8,[11,43],859⟩, ⟨83,8,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],954⟩, ⟨83,8,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],1201⟩],
  [],
  [⟨83,10,[10,42],32⟩, ⟨83,10,[9,41],58⟩, ⟨83,10,[2,34],110⟩, ⟨83,10,[8,40],153⟩, ⟨83,10,[0,32],193⟩, ⟨83,10,[1,3,33,35],510⟩, ⟨83,10,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],548⟩, ⟨83,10,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨83,10,[11,43],864⟩, ⟨83,10,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],961⟩, ⟨83,10,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],1213⟩],
  [⟨83,11,[-1],903⟩],
  [⟨83,12,[-1],583⟩],
  [],
  [⟨83,14,[-1],584⟩],
  [⟨83,15,[-1],586⟩],
  [⟨83,16,[-1],739⟩],
  [],
  [],
  [],
  [⟨83,20,[-1],739⟩],
  [],
  [],
  [],
  [⟨83,24,[-1],739⟩],
  [⟨83,25,[-1],739⟩],
  [⟨83,26,[-1],739⟩],
  [],
  [⟨83,28,[-1],739⟩],
  [⟨83,29,[-1],739⟩],
  [⟨83,30,[-1],739⟩],
  []
]

private def branchRecords_83 : List (List MiddleCertRecord) := [
  [],
  [⟨84,1,[-1],407⟩],
  [⟨84,2,[-1],739⟩],
  [⟨84,3,[-1],739⟩],
  [],
  [],
  [],
  [⟨84,7,[-1],739⟩],
  [⟨84,8,[-1],745⟩],
  [⟨84,9,[-1],745⟩],
  [],
  [⟨84,11,[-1],1137⟩],
  [],
  [⟨84,13,[-1],1138⟩],
  [],
  [],
  [],
  [⟨84,17,[-1],407⟩],
  [⟨84,18,[-1],739⟩],
  [⟨84,19,[-1],739⟩],
  [],
  [],
  [],
  [⟨84,23,[-1],739⟩],
  [⟨84,24,[-1],749⟩],
  [⟨84,25,[-1],749⟩],
  [],
  [⟨84,27,[-1],1137⟩],
  [],
  [⟨84,29,[-1],1139⟩],
  [],
  []
]

private def branchRecords_84 : List (List MiddleCertRecord) := [
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  []
]

private def branchRecords_85 : List (List MiddleCertRecord) := [
  [⟨86,0,[-1],533⟩],
  [⟨86,1,[-1],534⟩],
  [⟨86,2,[10,42],33⟩, ⟨86,2,[9,41],59⟩, ⟨86,2,[2,34],111⟩, ⟨86,2,[8,40],154⟩, ⟨86,2,[0,32],194⟩, ⟨86,2,[1,3,33,35],511⟩, ⟨86,2,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],549⟩, ⟨86,2,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨86,2,[11,43],865⟩, ⟨86,2,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],962⟩, ⟨86,2,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],1214⟩],
  [⟨86,3,[10,42],41⟩, ⟨86,3,[9,41],74⟩, ⟨86,3,[2,34],118⟩, ⟨86,3,[8,40],164⟩, ⟨86,3,[0,32],210⟩, ⟨86,3,[1,3,33,35],520⟩, ⟨86,3,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],559⟩, ⟨86,3,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨86,3,[11,43],872⟩, ⟨86,3,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],972⟩, ⟨86,3,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],1229⟩],
  [⟨86,4,[10,42],31⟩, ⟨86,4,[9,41],54⟩, ⟨86,4,[2,34],109⟩, ⟨86,4,[8,40],151⟩, ⟨86,4,[0,32],187⟩, ⟨86,4,[1,3,33,35],507⟩, ⟨86,4,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],545⟩, ⟨86,4,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨86,4,[11,43],862⟩, ⟨86,4,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],958⟩, ⟨86,4,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],1206⟩],
  [⟨86,5,[10,42],44⟩, ⟨86,5,[9,41],81⟩, ⟨86,5,[2,34],121⟩, ⟨86,5,[8,40],167⟩, ⟨86,5,[0,32],215⟩, ⟨86,5,[1,3,33,35],525⟩, ⟨86,5,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],563⟩, ⟨86,5,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨86,5,[11,43],875⟩, ⟨86,5,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],976⟩, ⟨86,5,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],1236⟩],
  [⟨86,6,[10,42],46⟩, ⟨86,6,[9,41],83⟩, ⟨86,6,[2,34],123⟩, ⟨86,6,[8,40],169⟩, ⟨86,6,[0,32],217⟩, ⟨86,6,[1,3,33,35],528⟩, ⟨86,6,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],565⟩, ⟨86,6,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨86,6,[11,43],877⟩, ⟨86,6,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],978⟩, ⟨86,6,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],1238⟩],
  [⟨86,7,[10,42],39⟩, ⟨86,7,[9,41],70⟩, ⟨86,7,[2,34],116⟩, ⟨86,7,[8,40],160⟩, ⟨86,7,[0,32],205⟩, ⟨86,7,[1,3,33,35],517⟩, ⟨86,7,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],555⟩, ⟨86,7,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨86,7,[11,43],870⟩, ⟨86,7,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],968⟩, ⟨86,7,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],1225⟩],
  [⟨86,8,[-1],621⟩],
  [⟨86,9,[-1],630⟩],
  [⟨86,10,[-1],624⟩],
  [⟨86,11,[-1],627⟩],
  [⟨86,12,[-1],1185⟩],
  [⟨86,13,[-1],1187⟩],
  [⟨86,14,[-1],1186⟩],
  [⟨86,15,[-1],1188⟩]
]

private def branchRecords_86 : List (List MiddleCertRecord) := [
  [⟨87,0,[-1],337⟩],
  [⟨87,1,[-1],339⟩],
  [⟨87,2,[-1],341⟩],
  [⟨87,3,[-1],922⟩],
  [⟨87,4,[-1],609⟩],
  [⟨87,5,[-1],1183⟩],
  [⟨87,6,[-1],775⟩],
  [⟨87,7,[-1],602⟩],
  [⟨87,8,[-1],836⟩],
  [⟨87,9,[-1],843⟩],
  [⟨87,10,[-1],846⟩],
  [⟨87,11,[-1],846⟩],
  [⟨87,12,[-1],1108⟩],
  [⟨87,13,[-1],1110⟩],
  [⟨87,14,[-1],1112⟩],
  [⟨87,15,[-1],1112⟩]
]

private def branchRecords_87 : List (List MiddleCertRecord) := [
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  []
]

private def branchRecords_88 : List (List MiddleCertRecord) := [
  [⟨89,0,[-1],87⟩],
  [⟨89,1,[-1],88⟩],
  [⟨89,2,[10],35⟩, ⟨89,2,[9],62⟩, ⟨89,2,[2],113⟩, ⟨89,2,[8],156⟩, ⟨89,2,[0],198⟩, ⟨89,2,[1,3],513⟩, ⟨89,2,[16,17,18,19,20,21,22,23],551⟩, ⟨89,2,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩, ⟨89,2,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨89,2,[11],867⟩, ⟨89,2,[24,25,26,27,28,29,30,31],964⟩, ⟨89,2,[4,5,6,7,12,13,14,15],1217⟩],
  [⟨89,3,[10],45⟩, ⟨89,3,[9],82⟩, ⟨89,3,[2],122⟩, ⟨89,3,[8],168⟩, ⟨89,3,[0],216⟩, ⟨89,3,[1,3],527⟩, ⟨89,3,[16,17,18,19,20,21,22,23],564⟩, ⟨89,3,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩, ⟨89,3,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨89,3,[11],876⟩, ⟨89,3,[24,25,26,27,28,29,30,31],977⟩, ⟨89,3,[4,5,6,7,12,13,14,15],1237⟩],
  [⟨89,4,[10],30⟩, ⟨89,4,[9],52⟩, ⟨89,4,[2],108⟩, ⟨89,4,[8],150⟩, ⟨89,4,[0],185⟩, ⟨89,4,[1,3],506⟩, ⟨89,4,[16,17,18,19,20,21,22,23],544⟩, ⟨89,4,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩, ⟨89,4,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨89,4,[11],861⟩, ⟨89,4,[24,25,26,27,28,29,30,31],957⟩, ⟨89,4,[4,5,6,7,12,13,14,15],1204⟩],
  [⟨89,5,[10],43⟩, ⟨89,5,[9],80⟩, ⟨89,5,[2],120⟩, ⟨89,5,[8],166⟩, ⟨89,5,[0],214⟩, ⟨89,5,[1,3],523⟩, ⟨89,5,[16,17,18,19,20,21,22,23],562⟩, ⟨89,5,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩, ⟨89,5,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨89,5,[11],874⟩, ⟨89,5,[24,25,26,27,28,29,30,31],975⟩, ⟨89,5,[4,5,6,7,12,13,14,15],1234⟩],
  [⟨89,6,[10],38⟩, ⟨89,6,[9],68⟩, ⟨89,6,[2],115⟩, ⟨89,6,[8],159⟩, ⟨89,6,[0],203⟩, ⟨89,6,[1,3],516⟩, ⟨89,6,[16,17,18,19,20,21,22,23],554⟩, ⟨89,6,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩, ⟨89,6,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨89,6,[11],869⟩, ⟨89,6,[24,25,26,27,28,29,30,31],967⟩, ⟨89,6,[4,5,6,7,12,13,14,15],1222⟩],
  [⟨89,7,[10],36⟩, ⟨89,7,[9],65⟩, ⟨89,7,[2],114⟩, ⟨89,7,[8],158⟩, ⟨89,7,[0],201⟩, ⟨89,7,[1,3],515⟩, ⟨89,7,[16,17,18,19,20,21,22,23],553⟩, ⟨89,7,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩, ⟨89,7,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨89,7,[11],868⟩, ⟨89,7,[24,25,26,27,28,29,30,31],966⟩, ⟨89,7,[4,5,6,7,12,13,14,15],1220⟩],
  [⟨89,8,[-1],568⟩],
  [⟨89,9,[-1],575⟩],
  [⟨89,10,[-1],571⟩],
  [⟨89,11,[-1],572⟩],
  [⟨89,12,[-1],700⟩],
  [⟨89,13,[-1],703⟩],
  [⟨89,14,[-1],701⟩],
  [⟨89,15,[-1],702⟩]
]

private def branchRecords_89 : List (List MiddleCertRecord) := [
  [⟨90,0,[-1],470⟩],
  [⟨90,1,[-1],469⟩],
  [⟨90,2,[-1],470⟩],
  [⟨90,3,[-1],470⟩],
  [⟨90,4,[-1],1083⟩],
  [⟨90,5,[-1],1032⟩],
  [⟨90,6,[-1],907⟩],
  [⟨90,7,[-1],615⟩],
  [⟨90,8,[-1],722⟩],
  [⟨90,9,[-1],720⟩],
  [⟨90,10,[-1],722⟩],
  [⟨90,11,[-1],722⟩],
  [⟨90,12,[-1],1166⟩],
  [⟨90,13,[-1],1165⟩],
  [⟨90,14,[-1],1166⟩],
  [⟨90,15,[-1],1166⟩]
]

private def branchRecords_90 : List (List MiddleCertRecord) := [
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  []
]

private def branchRecords_91 : List (List MiddleCertRecord) := [
  [⟨92,0,[-1],12⟩],
  [⟨92,1,[-1],13⟩],
  [⟨92,2,[9,41],56⟩, ⟨92,2,[8,40],152⟩, ⟨92,2,[0,32],190⟩, ⟨92,2,[1,33],508⟩, ⟨92,2,[16,17,48,49],546⟩, ⟨92,2,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩, ⟨92,2,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨92,2,[24,25,56,57],959⟩, ⟨92,2,[4,5,12,13,20,21,28,29,36,37,44,45,52,53,60,61],1218⟩],
  [⟨92,3,[9,41],86⟩, ⟨92,3,[8,40],171⟩, ⟨92,3,[0,32],220⟩, ⟨92,3,[1,33],530⟩, ⟨92,3,[16,17,48,49],567⟩, ⟨92,3,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩, ⟨92,3,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨92,3,[24,25,56,57],980⟩, ⟨92,3,[4,5,12,13,20,21,28,29,36,37,44,45,52,53,60,61],1218⟩],
  [⟨92,4,[9,41],50⟩, ⟨92,4,[8,40],148⟩, ⟨92,4,[0,32],183⟩, ⟨92,4,[1,33],502⟩, ⟨92,4,[16,17,48,49],540⟩, ⟨92,4,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩, ⟨92,4,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨92,4,[24,25,56,57],953⟩, ⟨92,4,[4,5,12,13,20,21,28,29,36,37,44,45,52,53,60,61],1218⟩],
  [⟨92,5,[9,41],84⟩, ⟨92,5,[8,40],170⟩, ⟨92,5,[0,32],218⟩, ⟨92,5,[1,33],529⟩, ⟨92,5,[16,17,48,49],566⟩, ⟨92,5,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩, ⟨92,5,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨92,5,[24,25,56,57],979⟩, ⟨92,5,[4,5,12,13,20,21,28,29,36,37,44,45,52,53,60,61],1218⟩],
  [⟨92,6,[9,41],64⟩, ⟨92,6,[8,40],157⟩, ⟨92,6,[0,32],200⟩, ⟨92,6,[1,33],514⟩, ⟨92,6,[16,17,48,49],552⟩, ⟨92,6,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩, ⟨92,6,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨92,6,[24,25,56,57],965⟩, ⟨92,6,[4,5,12,13,20,21,28,29,36,37,44,45,52,53,60,61],1218⟩],
  [⟨92,7,[9,41],71⟩, ⟨92,7,[8,40],161⟩, ⟨92,7,[0,32],206⟩, ⟨92,7,[1,33],518⟩, ⟨92,7,[16,17,48,49],556⟩, ⟨92,7,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩, ⟨92,7,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨92,7,[24,25,56,57],969⟩, ⟨92,7,[4,5,12,13,20,21,28,29,36,37,44,45,52,53,60,61],1218⟩],
  [⟨92,8,[-1],644⟩],
  [⟨92,9,[-1],651⟩],
  [⟨92,10,[-1],646⟩],
  [⟨92,11,[-1],648⟩],
  [⟨92,12,[-1],693⟩],
  [⟨92,13,[-1],696⟩],
  [⟨92,14,[-1],694⟩],
  [⟨92,15,[-1],695⟩]
]

private def branchRecords_92 : List (List MiddleCertRecord) := [
  [⟨93,0,[-1],9⟩],
  [⟨93,1,[-1],9⟩],
  [⟨93,2,[-1],9⟩],
  [⟨93,3,[-1],9⟩],
  [⟨93,4,[-1],593⟩],
  [⟨93,5,[-1],706⟩],
  [⟨93,6,[-1],600⟩],
  [⟨93,7,[-1],1003⟩],
  [⟨93,8,[-1],764⟩],
  [⟨93,9,[-1],764⟩],
  [⟨93,10,[-1],764⟩],
  [⟨93,11,[-1],764⟩],
  [⟨93,12,[-1],688⟩],
  [⟨93,13,[-1],688⟩],
  [⟨93,14,[-1],688⟩],
  [⟨93,15,[-1],688⟩]
]

private def branchRecords_93 : List (List MiddleCertRecord) := [
  [⟨94,0,[-1],278⟩],
  [⟨94,1,[-1],281⟩],
  [⟨94,2,[-1],279⟩],
  [⟨94,3,[-1],279⟩],
  [⟨94,4,[-1],631⟩],
  [⟨94,5,[-1],639⟩],
  [⟨94,6,[-1],632⟩],
  [⟨94,7,[-1],632⟩],
  [⟨94,8,[10],27⟩, ⟨94,8,[9],47⟩, ⟨94,8,[2],105⟩, ⟨94,8,[8],146⟩, ⟨94,8,[0],180⟩, ⟨94,8,[1,3],500⟩, ⟨94,8,[16,17,18,19,20,21,22,23],538⟩, ⟨94,8,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩, ⟨94,8,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨94,8,[11],857⟩, ⟨94,8,[24,25,26,27,28,29,30,31],951⟩, ⟨94,8,[4,5,6,7,12,13,14,15],1199⟩],
  [⟨94,9,[10],42⟩, ⟨94,9,[9],75⟩, ⟨94,9,[2],119⟩, ⟨94,9,[8],165⟩, ⟨94,9,[0],211⟩, ⟨94,9,[1,3],521⟩, ⟨94,9,[16,17,18,19,20,21,22,23],560⟩, ⟨94,9,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩, ⟨94,9,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨94,9,[11],873⟩, ⟨94,9,[24,25,26,27,28,29,30,31],973⟩, ⟨94,9,[4,5,6,7,12,13,14,15],1230⟩],
  [⟨94,10,[10],28⟩, ⟨94,10,[9],49⟩, ⟨94,10,[2],106⟩, ⟨94,10,[8],147⟩, ⟨94,10,[0],182⟩, ⟨94,10,[1,3],501⟩, ⟨94,10,[16,17,18,19,20,21,22,23],539⟩, ⟨94,10,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩, ⟨94,10,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨94,10,[11],858⟩, ⟨94,10,[24,25,26,27,28,29,30,31],952⟩, ⟨94,10,[4,5,6,7,12,13,14,15],1200⟩],
  [⟨94,11,[10],28⟩, ⟨94,11,[9],49⟩, ⟨94,11,[2],106⟩, ⟨94,11,[8],147⟩, ⟨94,11,[0],182⟩, ⟨94,11,[1,3],501⟩, ⟨94,11,[16,17,18,19,20,21,22,23],539⟩, ⟨94,11,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩, ⟨94,11,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨94,11,[11],858⟩, ⟨94,11,[24,25,26,27,28,29,30,31],952⟩, ⟨94,11,[4,5,6,7,12,13,14,15],1200⟩],
  [⟨94,12,[-1],631⟩],
  [⟨94,13,[-1],639⟩],
  [⟨94,14,[-1],632⟩],
  [⟨94,15,[-1],632⟩],
  [⟨94,16,[-1],653⟩],
  [⟨94,17,[-1],657⟩],
  [⟨94,18,[-1],654⟩],
  [⟨94,19,[-1],654⟩],
  [⟨94,20,[-1],653⟩],
  [⟨94,21,[-1],657⟩],
  [⟨94,22,[-1],654⟩],
  [⟨94,23,[-1],654⟩],
  [⟨94,24,[-1],986⟩],
  [⟨94,25,[-1],989⟩],
  [⟨94,26,[-1],987⟩],
  [⟨94,27,[-1],987⟩],
  [⟨94,28,[-1],986⟩],
  [⟨94,29,[-1],989⟩],
  [⟨94,30,[-1],987⟩],
  [⟨94,31,[-1],987⟩],
  [⟨94,32,[-1],278⟩],
  [⟨94,33,[-1],281⟩],
  [⟨94,34,[-1],280⟩],
  [⟨94,35,[-1],282⟩],
  [⟨94,36,[-1],631⟩],
  [⟨94,37,[-1],639⟩],
  [⟨94,38,[-1],636⟩],
  [⟨94,39,[-1],642⟩],
  [⟨94,40,[-1],582⟩],
  [⟨94,41,[-1],585⟩],
  [⟨94,42,[10],34⟩, ⟨94,42,[9],77⟩, ⟨94,42,[2],112⟩, ⟨94,42,[8],155⟩, ⟨94,42,[0],195⟩, ⟨94,42,[3],512⟩, ⟨94,42,[1],522⟩, ⟨94,42,[16,18,19,20,22,23],550⟩, ⟨94,42,[17,21],561⟩, ⟨94,42,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩, ⟨94,42,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨94,42,[11],866⟩, ⟨94,42,[24,26,27,28,30,31],963⟩, ⟨94,42,[25,29],974⟩, ⟨94,42,[4,6,7,12,14,15],1215⟩, ⟨94,42,[5,13],1231⟩],
  [⟨94,43,[10],40⟩, ⟨94,43,[9],77⟩, ⟨94,43,[2],117⟩, ⟨94,43,[8],163⟩, ⟨94,43,[0],207⟩, ⟨94,43,[3],519⟩, ⟨94,43,[1],522⟩, ⟨94,43,[16,18,19,20,22,23],558⟩, ⟨94,43,[17,21],561⟩, ⟨94,43,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩, ⟨94,43,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨94,43,[11],871⟩, ⟨94,43,[24,26,27,28,30,31],970⟩, ⟨94,43,[25,29],974⟩, ⟨94,43,[4,6,7,12,14,15],1227⟩, ⟨94,43,[5,13],1231⟩],
  [⟨94,44,[-1],631⟩],
  [⟨94,45,[-1],639⟩],
  [⟨94,46,[-1],636⟩],
  [⟨94,47,[-1],638⟩],
  [⟨94,48,[-1],653⟩],
  [⟨94,49,[-1],657⟩],
  [⟨94,50,[-1],655⟩],
  [⟨94,51,[-1],656⟩],
  [⟨94,52,[-1],653⟩],
  [⟨94,53,[-1],657⟩],
  [⟨94,54,[-1],655⟩],
  [⟨94,55,[-1],656⟩],
  [⟨94,56,[-1],986⟩],
  [⟨94,57,[-1],989⟩],
  [⟨94,58,[-1],988⟩],
  [⟨94,59,[-1],990⟩],
  [⟨94,60,[-1],986⟩],
  [⟨94,61,[-1],989⟩],
  [⟨94,62,[-1],988⟩],
  [⟨94,63,[-1],990⟩]
]

private def branchRecords_94 : List (List MiddleCertRecord) := [
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  []
]

private def branchRecords_95 : List (List MiddleCertRecord) := [
  [⟨96,0,[-1],505⟩],
  [⟨96,1,[-1],522⟩],
  [⟨96,2,[-1],504⟩],
  [⟨96,3,[-1],504⟩],
  [⟨96,4,[-1],1203⟩],
  [⟨96,5,[-1],1231⟩],
  [⟨96,6,[-1],1202⟩],
  [⟨96,7,[-1],1202⟩],
  [⟨96,8,[8,12,40,44],162⟩, ⟨96,8,[1,9],283⟩, ⟨96,8,[0],526⟩, ⟨96,8,[16,17,20,21,24,25,28,29],537⟩, ⟨96,8,[32,33,36,37,41,45,48,49,52,53,56,57,60,61],633⟩, ⟨96,8,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩, ⟨96,8,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨96,8,[4,5,13],1218⟩],
  [⟨96,9,[9],66⟩, ⟨96,9,[0,8],283⟩, ⟨96,9,[1],526⟩, ⟨96,9,[16,17,20,21,24,25,28,29],537⟩, ⟨96,9,[32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],633⟩, ⟨96,9,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩, ⟨96,9,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨96,9,[4,5,12,13],1218⟩],
  [⟨96,10,[10,14,42,46],37⟩, ⟨96,10,[2],526⟩, ⟨96,10,[18,22,26,30],537⟩, ⟨96,10,[34,35,38,39,43,47,50,54,58,59,62,63],633⟩, ⟨96,10,[0,1,4,5,8,9,12,13,16,17,20,21,24,25,28,29,32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],645⟩, ⟨96,10,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨96,10,[3,7,11,15,19,23,27,31,51,55],863⟩, ⟨96,10,[6],1218⟩],
  [⟨96,11,[-1],860⟩],
  [⟨96,12,[-1],1203⟩],
  [⟨96,13,[-1],1231⟩],
  [⟨96,14,[-1],1202⟩],
  [⟨96,15,[-1],1202⟩],
  [⟨96,16,[-1],543⟩],
  [⟨96,17,[-1],561⟩],
  [⟨96,18,[-1],542⟩],
  [⟨96,19,[-1],542⟩],
  [⟨96,20,[-1],543⟩],
  [⟨96,21,[-1],561⟩],
  [⟨96,22,[-1],542⟩],
  [⟨96,23,[-1],542⟩],
  [⟨96,24,[-1],956⟩],
  [⟨96,25,[-1],974⟩],
  [⟨96,26,[-1],955⟩],
  [⟨96,27,[-1],955⟩],
  [⟨96,28,[-1],956⟩],
  [⟨96,29,[-1],974⟩],
  [⟨96,30,[-1],955⟩],
  [⟨96,31,[-1],955⟩],
  [⟨96,32,[-1],505⟩],
  [⟨96,33,[-1],522⟩],
  [⟨96,34,[-1],509⟩],
  [⟨96,35,[-1],524⟩],
  [⟨96,36,[-1],1203⟩],
  [⟨96,37,[-1],1231⟩],
  [⟨96,38,[-1],1211⟩],
  [⟨96,39,[-1],1235⟩],
  [⟨96,40,[-1],634⟩],
  [⟨96,41,[-1],640⟩],
  [⟨96,42,[10,14,42,46],37⟩, ⟨96,42,[34],526⟩, ⟨96,42,[50,54,58,62],537⟩, ⟨96,42,[2,3,6,7,11,15,18,22,26,27,30,31],633⟩, ⟨96,42,[0,1,4,5,8,9,12,13,16,17,20,21,24,25,28,29,32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],645⟩, ⟨96,42,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨96,42,[19,23,35,39,43,47,51,55,59,63],863⟩, ⟨96,42,[38],1218⟩],
  [⟨96,43,[43],91⟩, ⟨96,43,[35],526⟩, ⟨96,43,[51,55,59,63],537⟩, ⟨96,43,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31],633⟩, ⟨96,43,[0,1,4,5,8,9,12,13,16,17,20,21,24,25,28,29,32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],645⟩, ⟨96,43,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ⟨96,43,[34,38,42,46,50,54,58,62],863⟩, ⟨96,43,[39,47],1218⟩],
  [⟨96,44,[-1],1203⟩],
  [⟨96,45,[-1],1231⟩],
  [⟨96,46,[-1],1211⟩],
  [⟨96,47,[-1],1223⟩],
  [⟨96,48,[-1],543⟩],
  [⟨96,49,[-1],561⟩],
  [⟨96,50,[-1],547⟩],
  [⟨96,51,[-1],557⟩],
  [⟨96,52,[-1],543⟩],
  [⟨96,53,[-1],561⟩],
  [⟨96,54,[-1],547⟩],
  [⟨96,55,[-1],557⟩],
  [⟨96,56,[-1],956⟩],
  [⟨96,57,[-1],974⟩],
  [⟨96,58,[-1],960⟩],
  [⟨96,59,[-1],971⟩],
  [⟨96,60,[-1],956⟩],
  [⟨96,61,[-1],974⟩],
  [⟨96,62,[-1],960⟩],
  [⟨96,63,[-1],971⟩]
]

private def branchRecords_96 : List (List MiddleCertRecord) := [
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  [],
  []
]

private def allBranchRecords : List (List (List MiddleCertRecord)) := [
  branchRecords_82,
  branchRecords_83,
  branchRecords_84,
  branchRecords_85,
  branchRecords_86,
  branchRecords_87,
  branchRecords_88,
  branchRecords_89,
  branchRecords_90,
  branchRecords_91,
  branchRecords_92,
  branchRecords_93,
  branchRecords_94,
  branchRecords_95,
  branchRecords_96
]

private def selectedRecords : List MiddleCertRecord := allBranchRecords.flatten.flatten

private theorem sub_82 (j : ℕ) (r : MiddleCertRecord)
    (h : r ∈ (branchRecords_82)[j]?.getD []) : r ∈ selectedRecords := by
  obtain ⟨rs, hrs, hr⟩ := getD_mem _ j r h
  refine List.mem_flatten.mpr ⟨rs, ?_, hr⟩
  exact List.mem_flatten.mpr ⟨branchRecords_82, by simp [allBranchRecords], hrs⟩

private theorem sub_83 (j : ℕ) (r : MiddleCertRecord)
    (h : r ∈ (branchRecords_83)[j]?.getD []) : r ∈ selectedRecords := by
  obtain ⟨rs, hrs, hr⟩ := getD_mem _ j r h
  refine List.mem_flatten.mpr ⟨rs, ?_, hr⟩
  exact List.mem_flatten.mpr ⟨branchRecords_83, by simp [allBranchRecords], hrs⟩

private theorem sub_84 (j : ℕ) (r : MiddleCertRecord)
    (h : r ∈ (branchRecords_84)[j]?.getD []) : r ∈ selectedRecords := by
  obtain ⟨rs, hrs, hr⟩ := getD_mem _ j r h
  refine List.mem_flatten.mpr ⟨rs, ?_, hr⟩
  exact List.mem_flatten.mpr ⟨branchRecords_84, by simp [allBranchRecords], hrs⟩

private theorem sub_85 (j : ℕ) (r : MiddleCertRecord)
    (h : r ∈ (branchRecords_85)[j]?.getD []) : r ∈ selectedRecords := by
  obtain ⟨rs, hrs, hr⟩ := getD_mem _ j r h
  refine List.mem_flatten.mpr ⟨rs, ?_, hr⟩
  exact List.mem_flatten.mpr ⟨branchRecords_85, by simp [allBranchRecords], hrs⟩

private theorem sub_86 (j : ℕ) (r : MiddleCertRecord)
    (h : r ∈ (branchRecords_86)[j]?.getD []) : r ∈ selectedRecords := by
  obtain ⟨rs, hrs, hr⟩ := getD_mem _ j r h
  refine List.mem_flatten.mpr ⟨rs, ?_, hr⟩
  exact List.mem_flatten.mpr ⟨branchRecords_86, by simp [allBranchRecords], hrs⟩

private theorem sub_87 (j : ℕ) (r : MiddleCertRecord)
    (h : r ∈ (branchRecords_87)[j]?.getD []) : r ∈ selectedRecords := by
  obtain ⟨rs, hrs, hr⟩ := getD_mem _ j r h
  refine List.mem_flatten.mpr ⟨rs, ?_, hr⟩
  exact List.mem_flatten.mpr ⟨branchRecords_87, by simp [allBranchRecords], hrs⟩

private theorem sub_88 (j : ℕ) (r : MiddleCertRecord)
    (h : r ∈ (branchRecords_88)[j]?.getD []) : r ∈ selectedRecords := by
  obtain ⟨rs, hrs, hr⟩ := getD_mem _ j r h
  refine List.mem_flatten.mpr ⟨rs, ?_, hr⟩
  exact List.mem_flatten.mpr ⟨branchRecords_88, by simp [allBranchRecords], hrs⟩

private theorem sub_89 (j : ℕ) (r : MiddleCertRecord)
    (h : r ∈ (branchRecords_89)[j]?.getD []) : r ∈ selectedRecords := by
  obtain ⟨rs, hrs, hr⟩ := getD_mem _ j r h
  refine List.mem_flatten.mpr ⟨rs, ?_, hr⟩
  exact List.mem_flatten.mpr ⟨branchRecords_89, by simp [allBranchRecords], hrs⟩

private theorem sub_90 (j : ℕ) (r : MiddleCertRecord)
    (h : r ∈ (branchRecords_90)[j]?.getD []) : r ∈ selectedRecords := by
  obtain ⟨rs, hrs, hr⟩ := getD_mem _ j r h
  refine List.mem_flatten.mpr ⟨rs, ?_, hr⟩
  exact List.mem_flatten.mpr ⟨branchRecords_90, by simp [allBranchRecords], hrs⟩

private theorem sub_91 (j : ℕ) (r : MiddleCertRecord)
    (h : r ∈ (branchRecords_91)[j]?.getD []) : r ∈ selectedRecords := by
  obtain ⟨rs, hrs, hr⟩ := getD_mem _ j r h
  refine List.mem_flatten.mpr ⟨rs, ?_, hr⟩
  exact List.mem_flatten.mpr ⟨branchRecords_91, by simp [allBranchRecords], hrs⟩

private theorem sub_92 (j : ℕ) (r : MiddleCertRecord)
    (h : r ∈ (branchRecords_92)[j]?.getD []) : r ∈ selectedRecords := by
  obtain ⟨rs, hrs, hr⟩ := getD_mem _ j r h
  refine List.mem_flatten.mpr ⟨rs, ?_, hr⟩
  exact List.mem_flatten.mpr ⟨branchRecords_92, by simp [allBranchRecords], hrs⟩

private theorem sub_93 (j : ℕ) (r : MiddleCertRecord)
    (h : r ∈ (branchRecords_93)[j]?.getD []) : r ∈ selectedRecords := by
  obtain ⟨rs, hrs, hr⟩ := getD_mem _ j r h
  refine List.mem_flatten.mpr ⟨rs, ?_, hr⟩
  exact List.mem_flatten.mpr ⟨branchRecords_93, by simp [allBranchRecords], hrs⟩

private theorem sub_94 (j : ℕ) (r : MiddleCertRecord)
    (h : r ∈ (branchRecords_94)[j]?.getD []) : r ∈ selectedRecords := by
  obtain ⟨rs, hrs, hr⟩ := getD_mem _ j r h
  refine List.mem_flatten.mpr ⟨rs, ?_, hr⟩
  exact List.mem_flatten.mpr ⟨branchRecords_94, by simp [allBranchRecords], hrs⟩

private theorem sub_95 (j : ℕ) (r : MiddleCertRecord)
    (h : r ∈ (branchRecords_95)[j]?.getD []) : r ∈ selectedRecords := by
  obtain ⟨rs, hrs, hr⟩ := getD_mem _ j r h
  refine List.mem_flatten.mpr ⟨rs, ?_, hr⟩
  exact List.mem_flatten.mpr ⟨branchRecords_95, by simp [allBranchRecords], hrs⟩

private theorem sub_96 (j : ℕ) (r : MiddleCertRecord)
    (h : r ∈ (branchRecords_96)[j]?.getD []) : r ∈ selectedRecords := by
  obtain ⟨rs, hrs, hr⟩ := getD_mem _ j r h
  refine List.mem_flatten.mpr ⟨rs, ?_, hr⟩
  exact List.mem_flatten.mpr ⟨branchRecords_96, by simp [allBranchRecords], hrs⟩

private def selectedGoals : List ℕ := [82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96]

private theorem records_eq :
    middleCertData.records.filter
      (fun r => decide ((middleCertGoal middleCertData r.goal).family = 5)) = selectedRecords := by
  decide +kernel

private theorem goals_eq :
    (List.range middleCertData.goals.length).filter
      (fun i => decide ((middleCertGoal middleCertData (i+1)).family = 5)) = selectedGoals := by
  decide +kernel

private theorem records_goals : ∀ r ∈ selectedRecords, r.goal ∈ goalIds := by
  decide +kernel

private def readyRows : List (MiddleCertRecord × (List MiddleCertBoundRef × RefComparison)) := [
  (⟨83,8,[10,42],29⟩, ([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.impossible)),
  (⟨83,8,[9,41],51⟩, ([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.impossible)),
  (⟨83,8,[2,34],107⟩, ([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.impossible)),
  (⟨83,8,[8,40],149⟩, ([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.impossible)),
  (⟨83,8,[0,32],184⟩, ([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.impossible)),
  (⟨83,8,[1,3,33,35],503⟩, ([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.impossible)),
  (⟨83,8,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],541⟩, ([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.impossible)),
  (⟨83,8,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.impossible)),
  (⟨83,8,[11,43],859⟩, ([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.impossible)),
  (⟨83,8,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],954⟩, ([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.impossible)),
  (⟨83,8,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],1201⟩, ([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.impossible)),
  (⟨83,10,[10,42],32⟩, ([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.impossible)),
  (⟨83,10,[9,41],58⟩, ([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.impossible)),
  (⟨83,10,[2,34],110⟩, ([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.impossible)),
  (⟨83,10,[8,40],153⟩, ([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.impossible)),
  (⟨83,10,[0,32],193⟩, ([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.impossible)),
  (⟨83,10,[1,3,33,35],510⟩, ([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.impossible)),
  (⟨83,10,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],548⟩, ([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.impossible)),
  (⟨83,10,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.impossible)),
  (⟨83,10,[11,43],864⟩, ([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.impossible)),
  (⟨83,10,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],961⟩, ([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.impossible)),
  (⟨83,10,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],1213⟩, ([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.impossible)),
  (⟨83,11,[-1],903⟩, ([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,true,221⟩,⟨true,true,591⟩,⟨false,false,215⟩],.bound ⟨true,false,538⟩)),
  (⟨83,12,[-1],583⟩, ([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,false,535⟩,⟨true,true,215⟩,⟨false,false,221⟩],.impossible)),
  (⟨83,14,[-1],584⟩, ([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.impossible)),
  (⟨83,15,[-1],586⟩, ([⟨false,false,633⟩,⟨false,true,603⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨true,true,591⟩],.bound ⟨true,false,538⟩)),
  (⟨83,16,[-1],739⟩, ([⟨true,true,633⟩,⟨false,false,666⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.bound ⟨false,false,580⟩)),
  (⟨83,20,[-1],739⟩, ([⟨true,true,633⟩,⟨false,false,666⟩,⟨true,false,535⟩,⟨true,true,215⟩,⟨false,false,221⟩],.bound ⟨false,false,580⟩)),
  (⟨83,24,[-1],739⟩, ([⟨true,true,633⟩,⟨true,true,666⟩,⟨true,false,535⟩,⟨false,false,215⟩,⟨false,false,221⟩],.bound ⟨false,false,763⟩)),
  (⟨83,25,[-1],739⟩, ([⟨true,true,633⟩,⟨true,true,666⟩,⟨false,false,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.bound ⟨false,false,639⟩)),
  (⟨83,26,[-1],739⟩, ([⟨true,true,633⟩,⟨true,true,666⟩,⟨true,true,221⟩,⟨false,false,215⟩,⟨false,false,591⟩],.bound ⟨false,false,560⟩)),
  (⟨83,28,[-1],739⟩, ([⟨true,true,633⟩,⟨true,true,666⟩,⟨true,false,535⟩,⟨true,true,215⟩,⟨false,false,221⟩],.bound ⟨false,false,763⟩)),
  (⟨83,29,[-1],739⟩, ([⟨true,true,633⟩,⟨true,true,666⟩,⟨true,true,215⟩,⟨false,false,221⟩,⟨false,true,535⟩],.bound ⟨false,false,639⟩)),
  (⟨83,30,[-1],739⟩, ([⟨true,true,633⟩,⟨true,true,666⟩,⟨true,true,215⟩,⟨true,true,221⟩,⟨false,false,591⟩],.bound ⟨false,false,560⟩)),
  (⟨84,1,[-1],407⟩, ([⟨true,false,601⟩,⟨false,false,629⟩,⟨false,false,634⟩,⟨false,false,633⟩,⟨false,true,601⟩],.impossible)),
  (⟨84,2,[-1],739⟩, ([⟨true,false,601⟩,⟨false,false,629⟩,⟨false,false,634⟩,⟨true,true,633⟩,⟨false,false,664⟩],.bound ⟨false,false,645⟩)),
  (⟨84,3,[-1],739⟩, ([⟨true,false,601⟩,⟨false,false,629⟩,⟨false,false,634⟩,⟨true,true,633⟩,⟨true,true,664⟩],.impossible)),
  (⟨84,7,[-1],739⟩, ([⟨false,false,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,633⟩,⟨true,true,664⟩],.bound ⟨false,false,635⟩)),
  (⟨84,8,[-1],745⟩, ([⟨true,true,634⟩,⟨false,false,629⟩,⟨false,false,664⟩,⟨true,false,601⟩,⟨false,false,633⟩],.bound ⟨true,false,645⟩)),
  (⟨84,9,[-1],745⟩, ([⟨true,true,634⟩,⟨false,false,629⟩,⟨false,false,664⟩,⟨false,false,633⟩,⟨false,true,601⟩],.impossible)),
  (⟨84,11,[-1],1137⟩, ([⟨true,true,634⟩,⟨false,false,629⟩,⟨false,false,664⟩,⟨true,true,633⟩,⟨true,true,664⟩],.impossible)),
  (⟨84,13,[-1],1138⟩, ([⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,629⟩,⟨false,false,633⟩,⟨false,true,601⟩],.bound ⟨true,false,635⟩)),
  (⟨84,17,[-1],407⟩, ([⟨true,false,601⟩,⟨true,true,629⟩,⟨false,false,634⟩,⟨false,false,633⟩,⟨false,true,601⟩],.impossible)),
  (⟨84,18,[-1],739⟩, ([⟨true,false,601⟩,⟨true,true,629⟩,⟨false,false,634⟩,⟨true,true,633⟩,⟨false,false,664⟩],.bound ⟨false,false,645⟩)),
  (⟨84,19,[-1],739⟩, ([⟨true,false,601⟩,⟨true,true,629⟩,⟨false,false,634⟩,⟨true,true,633⟩,⟨true,true,664⟩],.impossible)),
  (⟨84,23,[-1],739⟩, ([⟨true,true,629⟩,⟨false,false,634⟩,⟨false,true,601⟩,⟨true,true,633⟩,⟨true,true,664⟩],.bound ⟨false,false,635⟩)),
  (⟨84,24,[-1],749⟩, ([⟨true,true,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,false,601⟩,⟨false,false,633⟩],.bound ⟨true,false,645⟩)),
  (⟨84,25,[-1],749⟩, ([⟨true,true,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨false,false,633⟩,⟨false,true,601⟩],.impossible)),
  (⟨84,27,[-1],1137⟩, ([⟨true,true,629⟩,⟨true,true,634⟩,⟨false,false,664⟩,⟨true,true,633⟩,⟨true,true,664⟩],.impossible)),
  (⟨84,29,[-1],1139⟩, ([⟨true,true,629⟩,⟨true,true,634⟩,⟨true,true,664⟩,⟨false,false,633⟩,⟨false,true,601⟩],.bound ⟨true,false,635⟩)),
  (⟨86,0,[-1],533⟩, ([⟨true,false,382⟩,⟨false,false,221⟩,⟨true,false,414⟩,⟨false,false,348⟩],.bound ⟨true,false,442⟩)),
  (⟨86,1,[-1],534⟩, ([⟨true,false,382⟩,⟨false,false,221⟩,⟨false,false,348⟩,⟨false,true,414⟩],.bound ⟨true,false,385⟩)),
  (⟨86,2,[10,42],33⟩, ([⟨true,false,382⟩,⟨false,false,221⟩,⟨true,true,348⟩,⟨false,false,435⟩],.bound ⟨true,false,381⟩)),
  (⟨86,2,[9,41],59⟩, ([⟨true,false,382⟩,⟨false,false,221⟩,⟨true,true,348⟩,⟨false,false,435⟩],.bound ⟨true,false,381⟩)),
  (⟨86,2,[2,34],111⟩, ([⟨true,false,382⟩,⟨false,false,221⟩,⟨true,true,348⟩,⟨false,false,435⟩],.bound ⟨true,false,381⟩)),
  (⟨86,2,[8,40],154⟩, ([⟨true,false,382⟩,⟨false,false,221⟩,⟨true,true,348⟩,⟨false,false,435⟩],.bound ⟨true,false,381⟩)),
  (⟨86,2,[0,32],194⟩, ([⟨true,false,382⟩,⟨false,false,221⟩,⟨true,true,348⟩,⟨false,false,435⟩],.bound ⟨true,false,381⟩)),
  (⟨86,2,[1,3,33,35],511⟩, ([⟨true,false,382⟩,⟨false,false,221⟩,⟨true,true,348⟩,⟨false,false,435⟩],.bound ⟨true,false,381⟩)),
  (⟨86,2,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],549⟩, ([⟨true,false,382⟩,⟨false,false,221⟩,⟨true,true,348⟩,⟨false,false,435⟩],.bound ⟨true,false,381⟩)),
  (⟨86,2,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨true,false,382⟩,⟨false,false,221⟩,⟨true,true,348⟩,⟨false,false,435⟩],.bound ⟨true,false,381⟩)),
  (⟨86,2,[11,43],865⟩, ([⟨true,false,382⟩,⟨false,false,221⟩,⟨true,true,348⟩,⟨false,false,435⟩],.bound ⟨true,false,381⟩)),
  (⟨86,2,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],962⟩, ([⟨true,false,382⟩,⟨false,false,221⟩,⟨true,true,348⟩,⟨false,false,435⟩],.bound ⟨true,false,381⟩)),
  (⟨86,2,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],1214⟩, ([⟨true,false,382⟩,⟨false,false,221⟩,⟨true,true,348⟩,⟨false,false,435⟩],.bound ⟨true,false,381⟩)),
  (⟨86,3,[10,42],41⟩, ([⟨true,false,382⟩,⟨false,false,221⟩,⟨true,true,348⟩,⟨true,true,435⟩],.bound ⟨true,false,436⟩)),
  (⟨86,3,[9,41],74⟩, ([⟨true,false,382⟩,⟨false,false,221⟩,⟨true,true,348⟩,⟨true,true,435⟩],.bound ⟨true,false,436⟩)),
  (⟨86,3,[2,34],118⟩, ([⟨true,false,382⟩,⟨false,false,221⟩,⟨true,true,348⟩,⟨true,true,435⟩],.bound ⟨true,false,436⟩)),
  (⟨86,3,[8,40],164⟩, ([⟨true,false,382⟩,⟨false,false,221⟩,⟨true,true,348⟩,⟨true,true,435⟩],.bound ⟨true,false,436⟩)),
  (⟨86,3,[0,32],210⟩, ([⟨true,false,382⟩,⟨false,false,221⟩,⟨true,true,348⟩,⟨true,true,435⟩],.bound ⟨true,false,436⟩)),
  (⟨86,3,[1,3,33,35],520⟩, ([⟨true,false,382⟩,⟨false,false,221⟩,⟨true,true,348⟩,⟨true,true,435⟩],.bound ⟨true,false,436⟩)),
  (⟨86,3,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],559⟩, ([⟨true,false,382⟩,⟨false,false,221⟩,⟨true,true,348⟩,⟨true,true,435⟩],.bound ⟨true,false,436⟩)),
  (⟨86,3,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨true,false,382⟩,⟨false,false,221⟩,⟨true,true,348⟩,⟨true,true,435⟩],.bound ⟨true,false,436⟩)),
  (⟨86,3,[11,43],872⟩, ([⟨true,false,382⟩,⟨false,false,221⟩,⟨true,true,348⟩,⟨true,true,435⟩],.bound ⟨true,false,436⟩)),
  (⟨86,3,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],972⟩, ([⟨true,false,382⟩,⟨false,false,221⟩,⟨true,true,348⟩,⟨true,true,435⟩],.bound ⟨true,false,436⟩)),
  (⟨86,3,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],1229⟩, ([⟨true,false,382⟩,⟨false,false,221⟩,⟨true,true,348⟩,⟨true,true,435⟩],.bound ⟨true,false,436⟩)),
  (⟨86,4,[10,42],31⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,false,414⟩,⟨false,false,348⟩],.bound ⟨true,false,306⟩)),
  (⟨86,4,[9,41],54⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,false,414⟩,⟨false,false,348⟩],.bound ⟨true,false,306⟩)),
  (⟨86,4,[2,34],109⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,false,414⟩,⟨false,false,348⟩],.bound ⟨true,false,306⟩)),
  (⟨86,4,[8,40],151⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,false,414⟩,⟨false,false,348⟩],.bound ⟨true,false,306⟩)),
  (⟨86,4,[0,32],187⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,false,414⟩,⟨false,false,348⟩],.bound ⟨true,false,306⟩)),
  (⟨86,4,[1,3,33,35],507⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,false,414⟩,⟨false,false,348⟩],.bound ⟨true,false,306⟩)),
  (⟨86,4,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],545⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,false,414⟩,⟨false,false,348⟩],.bound ⟨true,false,306⟩)),
  (⟨86,4,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,false,414⟩,⟨false,false,348⟩],.bound ⟨true,false,306⟩)),
  (⟨86,4,[11,43],862⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,false,414⟩,⟨false,false,348⟩],.bound ⟨true,false,306⟩)),
  (⟨86,4,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],958⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,false,414⟩,⟨false,false,348⟩],.bound ⟨true,false,306⟩)),
  (⟨86,4,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],1206⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,false,414⟩,⟨false,false,348⟩],.bound ⟨true,false,306⟩)),
  (⟨86,5,[10,42],44⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨false,true,414⟩],.bound ⟨true,false,329⟩)),
  (⟨86,5,[9,41],81⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨false,true,414⟩],.bound ⟨true,false,329⟩)),
  (⟨86,5,[2,34],121⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨false,true,414⟩],.bound ⟨true,false,329⟩)),
  (⟨86,5,[8,40],167⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨false,true,414⟩],.bound ⟨true,false,329⟩)),
  (⟨86,5,[0,32],215⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨false,true,414⟩],.bound ⟨true,false,329⟩)),
  (⟨86,5,[1,3,33,35],525⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨false,true,414⟩],.bound ⟨true,false,329⟩)),
  (⟨86,5,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],563⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨false,true,414⟩],.bound ⟨true,false,329⟩)),
  (⟨86,5,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨false,true,414⟩],.bound ⟨true,false,329⟩)),
  (⟨86,5,[11,43],875⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨false,true,414⟩],.bound ⟨true,false,329⟩)),
  (⟨86,5,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],976⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨false,true,414⟩],.bound ⟨true,false,329⟩)),
  (⟨86,5,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],1236⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨false,false,348⟩,⟨false,true,414⟩],.bound ⟨true,false,329⟩)),
  (⟨86,6,[10,42],46⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],.bound ⟨true,false,340⟩)),
  (⟨86,6,[9,41],83⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],.bound ⟨true,false,340⟩)),
  (⟨86,6,[2,34],123⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],.bound ⟨true,false,340⟩)),
  (⟨86,6,[8,40],169⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],.bound ⟨true,false,340⟩)),
  (⟨86,6,[0,32],217⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],.bound ⟨true,false,340⟩)),
  (⟨86,6,[1,3,33,35],528⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],.bound ⟨true,false,340⟩)),
  (⟨86,6,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],565⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],.bound ⟨true,false,340⟩)),
  (⟨86,6,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],.bound ⟨true,false,340⟩)),
  (⟨86,6,[11,43],877⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],.bound ⟨true,false,340⟩)),
  (⟨86,6,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],978⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],.bound ⟨true,false,340⟩)),
  (⟨86,6,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],1238⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨false,false,435⟩],.bound ⟨true,false,340⟩)),
  (⟨86,7,[10,42],39⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],.bound ⟨true,false,262⟩)),
  (⟨86,7,[9,41],70⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],.bound ⟨true,false,262⟩)),
  (⟨86,7,[2,34],116⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],.bound ⟨true,false,262⟩)),
  (⟨86,7,[8,40],160⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],.bound ⟨true,false,262⟩)),
  (⟨86,7,[0,32],205⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],.bound ⟨true,false,262⟩)),
  (⟨86,7,[1,3,33,35],517⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],.bound ⟨true,false,262⟩)),
  (⟨86,7,[16,17,18,19,20,21,22,23,48,49,50,51,52,53,54,55],555⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],.bound ⟨true,false,262⟩)),
  (⟨86,7,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],.bound ⟨true,false,262⟩)),
  (⟨86,7,[11,43],870⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],.bound ⟨true,false,262⟩)),
  (⟨86,7,[24,25,26,27,28,29,30,31,56,57,58,59,60,61,62,63],968⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],.bound ⟨true,false,262⟩)),
  (⟨86,7,[4,5,6,7,12,13,14,15,36,37,38,39,44,45,46,47],1225⟩, ([⟨false,false,221⟩,⟨false,true,382⟩,⟨true,true,348⟩,⟨true,true,435⟩],.bound ⟨true,false,262⟩)),
  (⟨86,8,[-1],621⟩, ([⟨true,true,221⟩,⟨false,false,384⟩,⟨true,false,414⟩,⟨false,false,348⟩],.bound ⟨true,false,331⟩)),
  (⟨86,9,[-1],630⟩, ([⟨true,true,221⟩,⟨false,false,384⟩,⟨false,false,348⟩,⟨false,true,414⟩],.bound ⟨true,false,353⟩)),
  (⟨86,10,[-1],624⟩, ([⟨true,true,221⟩,⟨false,false,384⟩,⟨true,true,348⟩,⟨false,false,435⟩],.bound ⟨true,false,368⟩)),
  (⟨86,11,[-1],627⟩, ([⟨true,true,221⟩,⟨false,false,384⟩,⟨true,true,348⟩,⟨true,true,435⟩],.bound ⟨true,false,270⟩)),
  (⟨86,12,[-1],1185⟩, ([⟨true,true,221⟩,⟨true,true,384⟩,⟨true,false,414⟩,⟨false,false,348⟩],.bound ⟨true,false,428⟩)),
  (⟨86,13,[-1],1187⟩, ([⟨true,true,221⟩,⟨true,true,384⟩,⟨false,false,348⟩,⟨false,true,414⟩],.bound ⟨true,false,397⟩)),
  (⟨86,14,[-1],1186⟩, ([⟨true,true,221⟩,⟨true,true,384⟩,⟨true,true,348⟩,⟨false,false,435⟩],.bound ⟨true,false,389⟩)),
  (⟨86,15,[-1],1188⟩, ([⟨true,true,221⟩,⟨true,true,384⟩,⟨true,true,348⟩,⟨true,true,435⟩],.bound ⟨true,false,421⟩)),
  (⟨87,0,[-1],337⟩, ([⟨true,false,528⟩,⟨false,false,613⟩,⟨true,false,596⟩,⟨false,false,264⟩],.bound ⟨false,false,284⟩)),
  (⟨87,1,[-1],339⟩, ([⟨true,false,528⟩,⟨false,false,613⟩,⟨false,false,264⟩,⟨false,true,596⟩],.bound ⟨false,false,244⟩)),
  (⟨87,2,[-1],341⟩, ([⟨true,false,528⟩,⟨false,false,613⟩,⟨true,true,264⟩,⟨false,false,655⟩],.bound ⟨false,false,228⟩)),
  (⟨87,3,[-1],922⟩, ([⟨true,false,528⟩,⟨false,false,613⟩,⟨true,true,264⟩,⟨true,true,655⟩],.bound ⟨false,false,256⟩)),
  (⟨87,4,[-1],609⟩, ([⟨false,false,613⟩,⟨false,true,528⟩,⟨true,false,596⟩,⟨false,false,264⟩],.bound ⟨false,false,371⟩)),
  (⟨87,5,[-1],1183⟩, ([⟨false,false,613⟩,⟨false,true,528⟩,⟨false,false,264⟩,⟨false,true,596⟩],.bound ⟨false,false,722⟩)),
  (⟨87,6,[-1],775⟩, ([⟨false,false,613⟩,⟨false,true,528⟩,⟨true,true,264⟩,⟨false,false,655⟩],.bound ⟨false,false,647⟩)),
  (⟨87,7,[-1],602⟩, ([⟨false,false,613⟩,⟨false,true,528⟩,⟨true,true,264⟩,⟨true,true,655⟩],.bound ⟨false,false,281⟩)),
  (⟨87,8,[-1],836⟩, ([⟨true,true,613⟩,⟨false,false,579⟩,⟨true,false,596⟩,⟨false,false,264⟩],.bound ⟨false,false,343⟩)),
  (⟨87,9,[-1],843⟩, ([⟨true,true,613⟩,⟨false,false,579⟩,⟨false,false,264⟩,⟨false,true,596⟩],.bound ⟨false,false,720⟩)),
  (⟨87,10,[-1],846⟩, ([⟨true,true,613⟩,⟨false,false,579⟩,⟨true,true,264⟩,⟨false,false,655⟩],.bound ⟨false,false,592⟩)),
  (⟨87,11,[-1],846⟩, ([⟨true,true,613⟩,⟨false,false,579⟩,⟨true,true,264⟩,⟨true,true,655⟩],.bound ⟨false,false,349⟩)),
  (⟨87,12,[-1],1108⟩, ([⟨true,true,579⟩,⟨true,true,613⟩,⟨true,false,596⟩,⟨false,false,264⟩],.bound ⟨false,false,257⟩)),
  (⟨87,13,[-1],1110⟩, ([⟨true,true,579⟩,⟨true,true,613⟩,⟨false,false,264⟩,⟨false,true,596⟩],.bound ⟨false,false,99⟩)),
  (⟨87,14,[-1],1112⟩, ([⟨true,true,579⟩,⟨true,true,613⟩,⟨true,true,264⟩,⟨false,false,655⟩],.bound ⟨false,false,362⟩)),
  (⟨87,15,[-1],1112⟩, ([⟨true,true,579⟩,⟨true,true,613⟩,⟨true,true,264⟩,⟨true,true,655⟩],.bound ⟨false,false,242⟩)),
  (⟨89,0,[-1],87⟩, ([⟨true,false,375⟩,⟨false,false,254⟩,⟨true,false,434⟩,⟨false,false,321⟩],.bound ⟨true,false,468⟩)),
  (⟨89,1,[-1],88⟩, ([⟨true,false,375⟩,⟨false,false,254⟩,⟨false,false,321⟩,⟨false,true,434⟩],.bound ⟨true,false,390⟩)),
  (⟨89,2,[10],35⟩, ([⟨true,false,375⟩,⟨false,false,254⟩,⟨true,true,321⟩,⟨false,false,454⟩],.bound ⟨true,false,383⟩)),
  (⟨89,2,[9],62⟩, ([⟨true,false,375⟩,⟨false,false,254⟩,⟨true,true,321⟩,⟨false,false,454⟩],.bound ⟨true,false,383⟩)),
  (⟨89,2,[2],113⟩, ([⟨true,false,375⟩,⟨false,false,254⟩,⟨true,true,321⟩,⟨false,false,454⟩],.bound ⟨true,false,383⟩)),
  (⟨89,2,[8],156⟩, ([⟨true,false,375⟩,⟨false,false,254⟩,⟨true,true,321⟩,⟨false,false,454⟩],.bound ⟨true,false,383⟩)),
  (⟨89,2,[0],198⟩, ([⟨true,false,375⟩,⟨false,false,254⟩,⟨true,true,321⟩,⟨false,false,454⟩],.bound ⟨true,false,383⟩)),
  (⟨89,2,[1,3],513⟩, ([⟨true,false,375⟩,⟨false,false,254⟩,⟨true,true,321⟩,⟨false,false,454⟩],.bound ⟨true,false,383⟩)),
  (⟨89,2,[16,17,18,19,20,21,22,23],551⟩, ([⟨true,false,375⟩,⟨false,false,254⟩,⟨true,true,321⟩,⟨false,false,454⟩],.bound ⟨true,false,383⟩)),
  (⟨89,2,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩, ([⟨true,false,375⟩,⟨false,false,254⟩,⟨true,true,321⟩,⟨false,false,454⟩],.bound ⟨true,false,383⟩)),
  (⟨89,2,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨true,false,375⟩,⟨false,false,254⟩,⟨true,true,321⟩,⟨false,false,454⟩],.bound ⟨true,false,383⟩)),
  (⟨89,2,[11],867⟩, ([⟨true,false,375⟩,⟨false,false,254⟩,⟨true,true,321⟩,⟨false,false,454⟩],.bound ⟨true,false,383⟩)),
  (⟨89,2,[24,25,26,27,28,29,30,31],964⟩, ([⟨true,false,375⟩,⟨false,false,254⟩,⟨true,true,321⟩,⟨false,false,454⟩],.bound ⟨true,false,383⟩)),
  (⟨89,2,[4,5,6,7,12,13,14,15],1217⟩, ([⟨true,false,375⟩,⟨false,false,254⟩,⟨true,true,321⟩,⟨false,false,454⟩],.bound ⟨true,false,383⟩)),
  (⟨89,3,[10],45⟩, ([⟨true,false,375⟩,⟨false,false,254⟩,⟨true,true,321⟩,⟨true,true,454⟩],.bound ⟨true,false,458⟩)),
  (⟨89,3,[9],82⟩, ([⟨true,false,375⟩,⟨false,false,254⟩,⟨true,true,321⟩,⟨true,true,454⟩],.bound ⟨true,false,458⟩)),
  (⟨89,3,[2],122⟩, ([⟨true,false,375⟩,⟨false,false,254⟩,⟨true,true,321⟩,⟨true,true,454⟩],.bound ⟨true,false,458⟩)),
  (⟨89,3,[8],168⟩, ([⟨true,false,375⟩,⟨false,false,254⟩,⟨true,true,321⟩,⟨true,true,454⟩],.bound ⟨true,false,458⟩)),
  (⟨89,3,[0],216⟩, ([⟨true,false,375⟩,⟨false,false,254⟩,⟨true,true,321⟩,⟨true,true,454⟩],.bound ⟨true,false,458⟩)),
  (⟨89,3,[1,3],527⟩, ([⟨true,false,375⟩,⟨false,false,254⟩,⟨true,true,321⟩,⟨true,true,454⟩],.bound ⟨true,false,458⟩)),
  (⟨89,3,[16,17,18,19,20,21,22,23],564⟩, ([⟨true,false,375⟩,⟨false,false,254⟩,⟨true,true,321⟩,⟨true,true,454⟩],.bound ⟨true,false,458⟩)),
  (⟨89,3,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩, ([⟨true,false,375⟩,⟨false,false,254⟩,⟨true,true,321⟩,⟨true,true,454⟩],.bound ⟨true,false,458⟩)),
  (⟨89,3,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨true,false,375⟩,⟨false,false,254⟩,⟨true,true,321⟩,⟨true,true,454⟩],.bound ⟨true,false,458⟩)),
  (⟨89,3,[11],876⟩, ([⟨true,false,375⟩,⟨false,false,254⟩,⟨true,true,321⟩,⟨true,true,454⟩],.bound ⟨true,false,458⟩)),
  (⟨89,3,[24,25,26,27,28,29,30,31],977⟩, ([⟨true,false,375⟩,⟨false,false,254⟩,⟨true,true,321⟩,⟨true,true,454⟩],.bound ⟨true,false,458⟩)),
  (⟨89,3,[4,5,6,7,12,13,14,15],1237⟩, ([⟨true,false,375⟩,⟨false,false,254⟩,⟨true,true,321⟩,⟨true,true,454⟩],.bound ⟨true,false,458⟩)),
  (⟨89,4,[10],30⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,false,434⟩,⟨false,false,321⟩],.bound ⟨true,false,261⟩)),
  (⟨89,4,[9],52⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,false,434⟩,⟨false,false,321⟩],.bound ⟨true,false,261⟩)),
  (⟨89,4,[2],108⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,false,434⟩,⟨false,false,321⟩],.bound ⟨true,false,261⟩)),
  (⟨89,4,[8],150⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,false,434⟩,⟨false,false,321⟩],.bound ⟨true,false,261⟩)),
  (⟨89,4,[0],185⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,false,434⟩,⟨false,false,321⟩],.bound ⟨true,false,261⟩)),
  (⟨89,4,[1,3],506⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,false,434⟩,⟨false,false,321⟩],.bound ⟨true,false,261⟩)),
  (⟨89,4,[16,17,18,19,20,21,22,23],544⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,false,434⟩,⟨false,false,321⟩],.bound ⟨true,false,261⟩)),
  (⟨89,4,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,false,434⟩,⟨false,false,321⟩],.bound ⟨true,false,261⟩)),
  (⟨89,4,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,false,434⟩,⟨false,false,321⟩],.bound ⟨true,false,261⟩)),
  (⟨89,4,[11],861⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,false,434⟩,⟨false,false,321⟩],.bound ⟨true,false,261⟩)),
  (⟨89,4,[24,25,26,27,28,29,30,31],957⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,false,434⟩,⟨false,false,321⟩],.bound ⟨true,false,261⟩)),
  (⟨89,4,[4,5,6,7,12,13,14,15],1204⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,false,434⟩,⟨false,false,321⟩],.bound ⟨true,false,261⟩)),
  (⟨89,5,[10],43⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨false,true,434⟩],.bound ⟨true,false,285⟩)),
  (⟨89,5,[9],80⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨false,true,434⟩],.bound ⟨true,false,285⟩)),
  (⟨89,5,[2],120⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨false,true,434⟩],.bound ⟨true,false,285⟩)),
  (⟨89,5,[8],166⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨false,true,434⟩],.bound ⟨true,false,285⟩)),
  (⟨89,5,[0],214⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨false,true,434⟩],.bound ⟨true,false,285⟩)),
  (⟨89,5,[1,3],523⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨false,true,434⟩],.bound ⟨true,false,285⟩)),
  (⟨89,5,[16,17,18,19,20,21,22,23],562⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨false,true,434⟩],.bound ⟨true,false,285⟩)),
  (⟨89,5,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨false,true,434⟩],.bound ⟨true,false,285⟩)),
  (⟨89,5,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨false,true,434⟩],.bound ⟨true,false,285⟩)),
  (⟨89,5,[11],874⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨false,true,434⟩],.bound ⟨true,false,285⟩)),
  (⟨89,5,[24,25,26,27,28,29,30,31],975⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨false,true,434⟩],.bound ⟨true,false,285⟩)),
  (⟨89,5,[4,5,6,7,12,13,14,15],1234⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨false,false,321⟩,⟨false,true,434⟩],.bound ⟨true,false,285⟩)),
  (⟨89,6,[10],38⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],.bound ⟨true,false,307⟩)),
  (⟨89,6,[9],68⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],.bound ⟨true,false,307⟩)),
  (⟨89,6,[2],115⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],.bound ⟨true,false,307⟩)),
  (⟨89,6,[8],159⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],.bound ⟨true,false,307⟩)),
  (⟨89,6,[0],203⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],.bound ⟨true,false,307⟩)),
  (⟨89,6,[1,3],516⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],.bound ⟨true,false,307⟩)),
  (⟨89,6,[16,17,18,19,20,21,22,23],554⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],.bound ⟨true,false,307⟩)),
  (⟨89,6,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],.bound ⟨true,false,307⟩)),
  (⟨89,6,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],.bound ⟨true,false,307⟩)),
  (⟨89,6,[11],869⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],.bound ⟨true,false,307⟩)),
  (⟨89,6,[24,25,26,27,28,29,30,31],967⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],.bound ⟨true,false,307⟩)),
  (⟨89,6,[4,5,6,7,12,13,14,15],1222⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨false,false,454⟩],.bound ⟨true,false,307⟩)),
  (⟨89,7,[10],36⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],.bound ⟨true,false,206⟩)),
  (⟨89,7,[9],65⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],.bound ⟨true,false,206⟩)),
  (⟨89,7,[2],114⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],.bound ⟨true,false,206⟩)),
  (⟨89,7,[8],158⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],.bound ⟨true,false,206⟩)),
  (⟨89,7,[0],201⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],.bound ⟨true,false,206⟩)),
  (⟨89,7,[1,3],515⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],.bound ⟨true,false,206⟩)),
  (⟨89,7,[16,17,18,19,20,21,22,23],553⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],.bound ⟨true,false,206⟩)),
  (⟨89,7,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],.bound ⟨true,false,206⟩)),
  (⟨89,7,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],.bound ⟨true,false,206⟩)),
  (⟨89,7,[11],868⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],.bound ⟨true,false,206⟩)),
  (⟨89,7,[24,25,26,27,28,29,30,31],966⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],.bound ⟨true,false,206⟩)),
  (⟨89,7,[4,5,6,7,12,13,14,15],1220⟩, ([⟨false,false,254⟩,⟨false,true,375⟩,⟨true,true,321⟩,⟨true,true,454⟩],.bound ⟨true,false,206⟩)),
  (⟨89,8,[-1],568⟩, ([⟨true,true,254⟩,⟨false,false,373⟩,⟨true,false,434⟩,⟨false,false,321⟩],.bound ⟨true,false,294⟩)),
  (⟨89,9,[-1],575⟩, ([⟨true,true,254⟩,⟨false,false,373⟩,⟨false,false,321⟩,⟨false,true,434⟩],.bound ⟨true,false,332⟩)),
  (⟨89,10,[-1],571⟩, ([⟨true,true,254⟩,⟨false,false,373⟩,⟨true,true,321⟩,⟨false,false,454⟩],.bound ⟨true,false,358⟩)),
  (⟨89,11,[-1],572⟩, ([⟨true,true,254⟩,⟨false,false,373⟩,⟨true,true,321⟩,⟨true,true,454⟩],.bound ⟨true,false,214⟩)),
  (⟨89,12,[-1],700⟩, ([⟨true,true,254⟩,⟨true,true,373⟩,⟨true,false,434⟩,⟨false,false,321⟩],.bound ⟨true,false,448⟩)),
  (⟨89,13,[-1],703⟩, ([⟨true,true,254⟩,⟨true,true,373⟩,⟨false,false,321⟩,⟨false,true,434⟩],.bound ⟨true,false,407⟩)),
  (⟨89,14,[-1],701⟩, ([⟨true,true,254⟩,⟨true,true,373⟩,⟨true,true,321⟩,⟨false,false,454⟩],.bound ⟨true,false,396⟩)),
  (⟨89,15,[-1],702⟩, ([⟨true,true,254⟩,⟨true,true,373⟩,⟨true,true,321⟩,⟨true,true,454⟩],.bound ⟨true,false,441⟩)),
  (⟨90,0,[-1],470⟩, ([⟨true,false,612⟩,⟨false,false,640⟩,⟨true,false,563⟩,⟨false,false,296⟩],.bound ⟨false,false,258⟩)),
  (⟨90,1,[-1],469⟩, ([⟨true,false,612⟩,⟨false,false,640⟩,⟨false,false,296⟩,⟨false,true,563⟩],.bound ⟨false,false,191⟩)),
  (⟨90,2,[-1],470⟩, ([⟨true,false,612⟩,⟨false,false,640⟩,⟨true,true,296⟩,⟨false,false,631⟩],.bound ⟨false,false,179⟩)),
  (⟨90,3,[-1],470⟩, ([⟨true,false,612⟩,⟨false,false,640⟩,⟨true,true,296⟩,⟨true,true,631⟩],.bound ⟨false,false,219⟩)),
  (⟨90,4,[-1],1083⟩, ([⟨false,false,640⟩,⟨false,true,612⟩,⟨true,false,563⟩,⟨false,false,296⟩],.bound ⟨false,false,398⟩)),
  (⟨90,5,[-1],1032⟩, ([⟨false,false,640⟩,⟨false,true,612⟩,⟨false,false,296⟩,⟨false,true,563⟩],.bound ⟨false,false,725⟩)),
  (⟨90,6,[-1],907⟩, ([⟨false,false,640⟩,⟨false,true,612⟩,⟨true,true,296⟩,⟨false,false,631⟩],.bound ⟨false,false,706⟩)),
  (⟨90,7,[-1],615⟩, ([⟨false,false,640⟩,⟨false,true,612⟩,⟨true,true,296⟩,⟨true,true,631⟩],.bound ⟨false,false,164⟩)),
  (⟨90,8,[-1],722⟩, ([⟨true,true,640⟩,⟨false,false,675⟩,⟨true,false,563⟩,⟨false,false,296⟩],.bound ⟨false,false,324⟩)),
  (⟨90,9,[-1],720⟩, ([⟨true,true,640⟩,⟨false,false,675⟩,⟨false,false,296⟩,⟨false,true,563⟩],.bound ⟨false,false,709⟩)),
  (⟨90,10,[-1],722⟩, ([⟨true,true,640⟩,⟨false,false,675⟩,⟨true,true,296⟩,⟨false,false,631⟩],.bound ⟨false,false,657⟩)),
  (⟨90,11,[-1],722⟩, ([⟨true,true,640⟩,⟨false,false,675⟩,⟨true,true,296⟩,⟨true,true,631⟩],.bound ⟨false,false,301⟩)),
  (⟨90,12,[-1],1166⟩, ([⟨true,true,640⟩,⟨true,true,675⟩,⟨true,false,563⟩,⟨false,false,296⟩],.bound ⟨false,false,220⟩)),
  (⟨90,13,[-1],1165⟩, ([⟨true,true,640⟩,⟨true,true,675⟩,⟨false,false,296⟩,⟨false,true,563⟩],.bound ⟨false,false,158⟩)),
  (⟨90,14,[-1],1166⟩, ([⟨true,true,640⟩,⟨true,true,675⟩,⟨true,true,296⟩,⟨false,false,631⟩],.bound ⟨false,false,380⟩)),
  (⟨90,15,[-1],1166⟩, ([⟨true,true,640⟩,⟨true,true,675⟩,⟨true,true,296⟩,⟨true,true,631⟩],.bound ⟨false,false,196⟩)),
  (⟨92,0,[-1],12⟩, ([⟨true,false,347⟩,⟨false,false,223⟩,⟨true,false,466⟩,⟨false,false,216⟩],.bound ⟨true,false,524⟩)),
  (⟨92,1,[-1],13⟩, ([⟨true,false,347⟩,⟨false,false,223⟩,⟨false,false,216⟩,⟨false,true,466⟩],.bound ⟨true,false,404⟩)),
  (⟨92,2,[9,41],56⟩, ([⟨true,false,347⟩,⟨false,false,223⟩,⟨true,true,216⟩,⟨false,false,497⟩],.bound ⟨true,false,395⟩)),
  (⟨92,2,[8,40],152⟩, ([⟨true,false,347⟩,⟨false,false,223⟩,⟨true,true,216⟩,⟨false,false,497⟩],.bound ⟨true,false,395⟩)),
  (⟨92,2,[0,32],190⟩, ([⟨true,false,347⟩,⟨false,false,223⟩,⟨true,true,216⟩,⟨false,false,497⟩],.bound ⟨true,false,395⟩)),
  (⟨92,2,[1,33],508⟩, ([⟨true,false,347⟩,⟨false,false,223⟩,⟨true,true,216⟩,⟨false,false,497⟩],.bound ⟨true,false,395⟩)),
  (⟨92,2,[16,17,48,49],546⟩, ([⟨true,false,347⟩,⟨false,false,223⟩,⟨true,true,216⟩,⟨false,false,497⟩],.bound ⟨true,false,395⟩)),
  (⟨92,2,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩, ([⟨true,false,347⟩,⟨false,false,223⟩,⟨true,true,216⟩,⟨false,false,497⟩],.bound ⟨true,false,395⟩)),
  (⟨92,2,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨true,false,347⟩,⟨false,false,223⟩,⟨true,true,216⟩,⟨false,false,497⟩],.bound ⟨true,false,395⟩)),
  (⟨92,2,[24,25,56,57],959⟩, ([⟨true,false,347⟩,⟨false,false,223⟩,⟨true,true,216⟩,⟨false,false,497⟩],.bound ⟨true,false,395⟩)),
  (⟨92,2,[4,5,12,13,20,21,28,29,36,37,44,45,52,53,60,61],1218⟩, ([⟨true,false,347⟩,⟨false,false,223⟩,⟨true,true,216⟩,⟨false,false,497⟩],.bound ⟨true,false,395⟩)),
  (⟨92,3,[9,41],86⟩, ([⟨true,false,347⟩,⟨false,false,223⟩,⟨true,true,216⟩,⟨true,true,497⟩],.bound ⟨true,false,512⟩)),
  (⟨92,3,[8,40],171⟩, ([⟨true,false,347⟩,⟨false,false,223⟩,⟨true,true,216⟩,⟨true,true,497⟩],.bound ⟨true,false,512⟩)),
  (⟨92,3,[0,32],220⟩, ([⟨true,false,347⟩,⟨false,false,223⟩,⟨true,true,216⟩,⟨true,true,497⟩],.bound ⟨true,false,512⟩)),
  (⟨92,3,[1,33],530⟩, ([⟨true,false,347⟩,⟨false,false,223⟩,⟨true,true,216⟩,⟨true,true,497⟩],.bound ⟨true,false,512⟩)),
  (⟨92,3,[16,17,48,49],567⟩, ([⟨true,false,347⟩,⟨false,false,223⟩,⟨true,true,216⟩,⟨true,true,497⟩],.bound ⟨true,false,512⟩)),
  (⟨92,3,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩, ([⟨true,false,347⟩,⟨false,false,223⟩,⟨true,true,216⟩,⟨true,true,497⟩],.bound ⟨true,false,512⟩)),
  (⟨92,3,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨true,false,347⟩,⟨false,false,223⟩,⟨true,true,216⟩,⟨true,true,497⟩],.bound ⟨true,false,512⟩)),
  (⟨92,3,[24,25,56,57],980⟩, ([⟨true,false,347⟩,⟨false,false,223⟩,⟨true,true,216⟩,⟨true,true,497⟩],.bound ⟨true,false,512⟩)),
  (⟨92,3,[4,5,12,13,20,21,28,29,36,37,44,45,52,53,60,61],1218⟩, ([⟨true,false,347⟩,⟨false,false,223⟩,⟨true,true,216⟩,⟨true,true,497⟩],.bound ⟨true,false,512⟩)),
  (⟨92,4,[9,41],50⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,false,466⟩,⟨false,false,216⟩],.bound ⟨true,false,140⟩)),
  (⟨92,4,[8,40],148⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,false,466⟩,⟨false,false,216⟩],.bound ⟨true,false,140⟩)),
  (⟨92,4,[0,32],183⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,false,466⟩,⟨false,false,216⟩],.bound ⟨true,false,140⟩)),
  (⟨92,4,[1,33],502⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,false,466⟩,⟨false,false,216⟩],.bound ⟨true,false,140⟩)),
  (⟨92,4,[16,17,48,49],540⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,false,466⟩,⟨false,false,216⟩],.bound ⟨true,false,140⟩)),
  (⟨92,4,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,false,466⟩,⟨false,false,216⟩],.bound ⟨true,false,140⟩)),
  (⟨92,4,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,false,466⟩,⟨false,false,216⟩],.bound ⟨true,false,140⟩)),
  (⟨92,4,[24,25,56,57],953⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,false,466⟩,⟨false,false,216⟩],.bound ⟨true,false,140⟩)),
  (⟨92,4,[4,5,12,13,20,21,28,29,36,37,44,45,52,53,60,61],1218⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,false,466⟩,⟨false,false,216⟩],.bound ⟨true,false,140⟩)),
  (⟨92,5,[9,41],84⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨false,false,216⟩,⟨false,true,466⟩],.bound ⟨true,false,186⟩)),
  (⟨92,5,[8,40],170⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨false,false,216⟩,⟨false,true,466⟩],.bound ⟨true,false,186⟩)),
  (⟨92,5,[0,32],218⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨false,false,216⟩,⟨false,true,466⟩],.bound ⟨true,false,186⟩)),
  (⟨92,5,[1,33],529⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨false,false,216⟩,⟨false,true,466⟩],.bound ⟨true,false,186⟩)),
  (⟨92,5,[16,17,48,49],566⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨false,false,216⟩,⟨false,true,466⟩],.bound ⟨true,false,186⟩)),
  (⟨92,5,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨false,false,216⟩,⟨false,true,466⟩],.bound ⟨true,false,186⟩)),
  (⟨92,5,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨false,false,216⟩,⟨false,true,466⟩],.bound ⟨true,false,186⟩)),
  (⟨92,5,[24,25,56,57],979⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨false,false,216⟩,⟨false,true,466⟩],.bound ⟨true,false,186⟩)),
  (⟨92,5,[4,5,12,13,20,21,28,29,36,37,44,45,52,53,60,61],1218⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨false,false,216⟩,⟨false,true,466⟩],.bound ⟨true,false,186⟩)),
  (⟨92,6,[9,41],64⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨false,false,497⟩],.bound ⟨true,false,205⟩)),
  (⟨92,6,[8,40],157⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨false,false,497⟩],.bound ⟨true,false,205⟩)),
  (⟨92,6,[0,32],200⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨false,false,497⟩],.bound ⟨true,false,205⟩)),
  (⟨92,6,[1,33],514⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨false,false,497⟩],.bound ⟨true,false,205⟩)),
  (⟨92,6,[16,17,48,49],552⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨false,false,497⟩],.bound ⟨true,false,205⟩)),
  (⟨92,6,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨false,false,497⟩],.bound ⟨true,false,205⟩)),
  (⟨92,6,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨false,false,497⟩],.bound ⟨true,false,205⟩)),
  (⟨92,6,[24,25,56,57],965⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨false,false,497⟩],.bound ⟨true,false,205⟩)),
  (⟨92,6,[4,5,12,13,20,21,28,29,36,37,44,45,52,53,60,61],1218⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨false,false,497⟩],.bound ⟨true,false,205⟩)),
  (⟨92,7,[9,41],71⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨true,true,497⟩],.bound ⟨true,false,95⟩)),
  (⟨92,7,[8,40],161⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨true,true,497⟩],.bound ⟨true,false,95⟩)),
  (⟨92,7,[0,32],206⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨true,true,497⟩],.bound ⟨true,false,95⟩)),
  (⟨92,7,[1,33],518⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨true,true,497⟩],.bound ⟨true,false,95⟩)),
  (⟨92,7,[16,17,48,49],556⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨true,true,497⟩],.bound ⟨true,false,95⟩)),
  (⟨92,7,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨true,true,497⟩],.bound ⟨true,false,95⟩)),
  (⟨92,7,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨true,true,497⟩],.bound ⟨true,false,95⟩)),
  (⟨92,7,[24,25,56,57],969⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨true,true,497⟩],.bound ⟨true,false,95⟩)),
  (⟨92,7,[4,5,12,13,20,21,28,29,36,37,44,45,52,53,60,61],1218⟩, ([⟨false,false,223⟩,⟨false,true,347⟩,⟨true,true,216⟩,⟨true,true,497⟩],.bound ⟨true,false,95⟩)),
  (⟨92,8,[-1],644⟩, ([⟨true,true,223⟩,⟨false,false,328⟩,⟨true,false,466⟩,⟨false,false,216⟩],.bound ⟨true,false,218⟩)),
  (⟨92,9,[-1],651⟩, ([⟨true,true,223⟩,⟨false,false,328⟩,⟨false,false,216⟩,⟨false,true,466⟩],.bound ⟨true,false,290⟩)),
  (⟨92,10,[-1],646⟩, ([⟨true,true,223⟩,⟨false,false,328⟩,⟨true,true,216⟩,⟨false,false,497⟩],.bound ⟨true,false,335⟩)),
  (⟨92,11,[-1],648⟩, ([⟨true,true,223⟩,⟨false,false,328⟩,⟨true,true,216⟩,⟨true,true,497⟩],.bound ⟨true,false,106⟩)),
  (⟨92,12,[-1],693⟩, ([⟨true,true,223⟩,⟨true,true,328⟩,⟨true,false,466⟩,⟨false,false,216⟩],.bound ⟨true,false,499⟩)),
  (⟨92,13,[-1],696⟩, ([⟨true,true,223⟩,⟨true,true,328⟩,⟨false,false,216⟩,⟨false,true,466⟩],.bound ⟨true,false,425⟩)),
  (⟨92,14,[-1],694⟩, ([⟨true,true,223⟩,⟨true,true,328⟩,⟨true,true,216⟩,⟨false,false,497⟩],.bound ⟨true,false,412⟩)),
  (⟨92,15,[-1],695⟩, ([⟨true,true,223⟩,⟨true,true,328⟩,⟨true,true,216⟩,⟨true,true,497⟩],.bound ⟨true,false,484⟩)),
  (⟨93,0,[-1],9⟩, ([⟨true,false,177⟩,⟨false,false,567⟩,⟨true,false,605⟩,⟨false,false,634⟩],.bound ⟨false,false,200⟩)),
  (⟨93,1,[-1],9⟩, ([⟨true,false,177⟩,⟨false,false,567⟩,⟨false,false,634⟩,⟨false,true,605⟩],.bound ⟨false,false,128⟩)),
  (⟨93,2,[-1],9⟩, ([⟨true,false,177⟩,⟨false,false,567⟩,⟨true,true,634⟩,⟨false,false,668⟩],.bound ⟨false,false,115⟩)),
  (⟨93,3,[-1],9⟩, ([⟨true,false,177⟩,⟨false,false,567⟩,⟨true,true,634⟩,⟨true,true,668⟩],.bound ⟨false,false,153⟩)),
  (⟨93,4,[-1],593⟩, ([⟨false,false,567⟩,⟨false,true,177⟩,⟨true,false,605⟩,⟨false,false,634⟩],.bound ⟨false,false,236⟩)),
  (⟨93,5,[-1],706⟩, ([⟨false,false,567⟩,⟨false,true,177⟩,⟨false,false,634⟩,⟨false,true,605⟩],.bound ⟨false,false,15⟩)),
  (⟨93,6,[-1],600⟩, ([⟨false,false,567⟩,⟨false,true,177⟩,⟨true,true,634⟩,⟨false,false,668⟩],.bound ⟨false,false,11⟩)),
  (⟨93,7,[-1],1003⟩, ([⟨false,false,567⟩,⟨false,true,177⟩,⟨true,true,634⟩,⟨true,true,668⟩],.bound ⟨false,false,716⟩)),
  (⟨93,8,[-1],764⟩, ([⟨true,true,567⟩,⟨false,false,110⟩,⟨true,false,605⟩,⟨false,false,634⟩],.bound ⟨false,false,267⟩)),
  (⟨93,9,[-1],764⟩, ([⟨true,true,567⟩,⟨false,false,110⟩,⟨false,false,634⟩,⟨false,true,605⟩],.bound ⟨false,false,746⟩)),
  (⟨93,10,[-1],764⟩, ([⟨true,true,567⟩,⟨false,false,110⟩,⟨true,true,634⟩,⟨false,false,668⟩],.bound ⟨false,false,731⟩)),
  (⟨93,11,[-1],764⟩, ([⟨true,true,567⟩,⟨false,false,110⟩,⟨true,true,634⟩,⟨true,true,668⟩],.bound ⟨false,false,121⟩)),
  (⟨93,12,[-1],688⟩, ([⟨true,true,110⟩,⟨true,true,567⟩,⟨true,false,605⟩,⟨false,false,634⟩],.bound ⟨false,false,154⟩)),
  (⟨93,13,[-1],688⟩, ([⟨true,true,110⟩,⟨true,true,567⟩,⟨false,false,634⟩,⟨false,true,605⟩],.bound ⟨false,false,208⟩)),
  (⟨93,14,[-1],688⟩, ([⟨true,true,110⟩,⟨true,true,567⟩,⟨true,true,634⟩,⟨false,false,668⟩],.bound ⟨false,false,476⟩)),
  (⟨93,15,[-1],688⟩, ([⟨true,true,110⟩,⟨true,true,567⟩,⟨true,true,634⟩,⟨true,true,668⟩],.bound ⟨false,false,130⟩)),
  (⟨94,0,[-1],278⟩, ([⟨true,false,426⟩,⟨false,false,215⟩,⟨false,false,264⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.bound ⟨true,false,523⟩)),
  (⟨94,1,[-1],281⟩, ([⟨true,false,426⟩,⟨false,false,215⟩,⟨false,false,264⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,419⟩)),
  (⟨94,2,[-1],279⟩, ([⟨true,false,426⟩,⟨false,false,215⟩,⟨false,false,264⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,365⟩)),
  (⟨94,3,[-1],279⟩, ([⟨true,false,426⟩,⟨false,false,215⟩,⟨false,false,264⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,511⟩)),
  (⟨94,4,[-1],631⟩, ([⟨true,false,426⟩,⟨false,false,215⟩,⟨false,false,264⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.bound ⟨true,false,523⟩)),
  (⟨94,5,[-1],639⟩, ([⟨true,false,426⟩,⟨false,false,215⟩,⟨false,false,264⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,419⟩)),
  (⟨94,6,[-1],632⟩, ([⟨true,false,426⟩,⟨false,false,215⟩,⟨false,false,264⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.bound ⟨true,false,365⟩)),
  (⟨94,7,[-1],632⟩, ([⟨true,false,426⟩,⟨false,false,215⟩,⟨false,false,264⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.bound ⟨true,false,511⟩)),
  (⟨94,8,[10],27⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.bound ⟨true,false,224⟩)),
  (⟨94,8,[9],47⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.bound ⟨true,false,224⟩)),
  (⟨94,8,[2],105⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.bound ⟨true,false,224⟩)),
  (⟨94,8,[8],146⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.bound ⟨true,false,224⟩)),
  (⟨94,8,[0],180⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.bound ⟨true,false,224⟩)),
  (⟨94,8,[1,3],500⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.bound ⟨true,false,224⟩)),
  (⟨94,8,[16,17,18,19,20,21,22,23],538⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.bound ⟨true,false,224⟩)),
  (⟨94,8,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.bound ⟨true,false,224⟩)),
  (⟨94,8,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.bound ⟨true,false,224⟩)),
  (⟨94,8,[11],857⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.bound ⟨true,false,224⟩)),
  (⟨94,8,[24,25,26,27,28,29,30,31],951⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.bound ⟨true,false,224⟩)),
  (⟨94,8,[4,5,6,7,12,13,14,15],1199⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.bound ⟨true,false,224⟩)),
  (⟨94,9,[10],42⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,185⟩)),
  (⟨94,9,[9],75⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,185⟩)),
  (⟨94,9,[2],119⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,185⟩)),
  (⟨94,9,[8],165⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,185⟩)),
  (⟨94,9,[0],211⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,185⟩)),
  (⟨94,9,[1,3],521⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,185⟩)),
  (⟨94,9,[16,17,18,19,20,21,22,23],560⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,185⟩)),
  (⟨94,9,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,185⟩)),
  (⟨94,9,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,185⟩)),
  (⟨94,9,[11],873⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,185⟩)),
  (⟨94,9,[24,25,26,27,28,29,30,31],973⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,185⟩)),
  (⟨94,9,[4,5,6,7,12,13,14,15],1230⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,185⟩)),
  (⟨94,10,[10],28⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩)),
  (⟨94,10,[9],49⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩)),
  (⟨94,10,[2],106⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩)),
  (⟨94,10,[8],147⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩)),
  (⟨94,10,[0],182⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩)),
  (⟨94,10,[1,3],501⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩)),
  (⟨94,10,[16,17,18,19,20,21,22,23],539⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩)),
  (⟨94,10,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩)),
  (⟨94,10,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩)),
  (⟨94,10,[11],858⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩)),
  (⟨94,10,[24,25,26,27,28,29,30,31],952⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩)),
  (⟨94,10,[4,5,6,7,12,13,14,15],1200⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩)),
  (⟨94,11,[10],28⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,137⟩)),
  (⟨94,11,[9],49⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,137⟩)),
  (⟨94,11,[2],106⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,137⟩)),
  (⟨94,11,[8],147⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,137⟩)),
  (⟨94,11,[0],182⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,137⟩)),
  (⟨94,11,[1,3],501⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,137⟩)),
  (⟨94,11,[16,17,18,19,20,21,22,23],539⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,137⟩)),
  (⟨94,11,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,137⟩)),
  (⟨94,11,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,137⟩)),
  (⟨94,11,[11],858⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,137⟩)),
  (⟨94,11,[24,25,26,27,28,29,30,31],952⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,137⟩)),
  (⟨94,11,[4,5,6,7,12,13,14,15],1200⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,137⟩)),
  (⟨94,12,[-1],631⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.bound ⟨true,false,224⟩)),
  (⟨94,13,[-1],639⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,185⟩)),
  (⟨94,14,[-1],632⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩)),
  (⟨94,15,[-1],632⟩, ([⟨false,false,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.bound ⟨true,false,137⟩)),
  (⟨94,16,[-1],653⟩, ([⟨true,true,264⟩,⟨false,false,215⟩,⟨false,false,446⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.bound ⟨true,false,249⟩)),
  (⟨94,17,[-1],657⟩, ([⟨true,true,264⟩,⟨false,false,215⟩,⟨false,false,446⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,204⟩)),
  (⟨94,18,[-1],654⟩, ([⟨true,true,264⟩,⟨false,false,215⟩,⟨false,false,446⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,334⟩)),
  (⟨94,19,[-1],654⟩, ([⟨true,true,264⟩,⟨false,false,215⟩,⟨false,false,446⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,142⟩)),
  (⟨94,20,[-1],653⟩, ([⟨true,true,264⟩,⟨false,false,215⟩,⟨false,false,446⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.bound ⟨true,false,249⟩)),
  (⟨94,21,[-1],657⟩, ([⟨true,true,264⟩,⟨false,false,215⟩,⟨false,false,446⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,204⟩)),
  (⟨94,22,[-1],654⟩, ([⟨true,true,264⟩,⟨false,false,215⟩,⟨false,false,446⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.bound ⟨true,false,334⟩)),
  (⟨94,23,[-1],654⟩, ([⟨true,true,264⟩,⟨false,false,215⟩,⟨false,false,446⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.bound ⟨true,false,142⟩)),
  (⟨94,24,[-1],986⟩, ([⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.bound ⟨true,false,498⟩)),
  (⟨94,25,[-1],989⟩, ([⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,460⟩)),
  (⟨94,26,[-1],987⟩, ([⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,405⟩)),
  (⟨94,27,[-1],987⟩, ([⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,483⟩)),
  (⟨94,28,[-1],986⟩, ([⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.bound ⟨true,false,498⟩)),
  (⟨94,29,[-1],989⟩, ([⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,460⟩)),
  (⟨94,30,[-1],987⟩, ([⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.bound ⟨true,false,405⟩)),
  (⟨94,31,[-1],987⟩, ([⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,215⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.bound ⟨true,false,483⟩)),
  (⟨94,32,[-1],278⟩, ([⟨true,false,426⟩,⟨true,true,215⟩,⟨false,false,264⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.bound ⟨true,false,523⟩)),
  (⟨94,33,[-1],281⟩, ([⟨true,false,426⟩,⟨true,true,215⟩,⟨false,false,264⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,419⟩)),
  (⟨94,34,[-1],280⟩, ([⟨true,false,426⟩,⟨true,true,215⟩,⟨false,false,264⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,365⟩)),
  (⟨94,35,[-1],282⟩, ([⟨true,false,426⟩,⟨true,true,215⟩,⟨false,false,264⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,511⟩)),
  (⟨94,36,[-1],631⟩, ([⟨true,false,426⟩,⟨true,true,215⟩,⟨false,false,264⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.bound ⟨true,false,523⟩)),
  (⟨94,37,[-1],639⟩, ([⟨true,false,426⟩,⟨true,true,215⟩,⟨false,false,264⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,419⟩)),
  (⟨94,38,[-1],636⟩, ([⟨true,false,426⟩,⟨true,true,215⟩,⟨false,false,264⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.bound ⟨true,false,365⟩)),
  (⟨94,39,[-1],642⟩, ([⟨true,false,426⟩,⟨true,true,215⟩,⟨false,false,264⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.bound ⟨true,false,511⟩)),
  (⟨94,40,[-1],582⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.bound ⟨true,false,224⟩)),
  (⟨94,41,[-1],585⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,185⟩)),
  (⟨94,42,[10],34⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩)),
  (⟨94,42,[9],77⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩)),
  (⟨94,42,[2],112⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩)),
  (⟨94,42,[8],155⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩)),
  (⟨94,42,[0],195⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩)),
  (⟨94,42,[3],512⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩)),
  (⟨94,42,[1],522⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩)),
  (⟨94,42,[16,18,19,20,22,23],550⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩)),
  (⟨94,42,[17,21],561⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩)),
  (⟨94,42,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩)),
  (⟨94,42,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩)),
  (⟨94,42,[11],866⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩)),
  (⟨94,42,[24,26,27,28,30,31],963⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩)),
  (⟨94,42,[25,29],974⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩)),
  (⟨94,42,[4,6,7,12,14,15],1215⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩)),
  (⟨94,42,[5,13],1231⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩)),
  (⟨94,43,[10],40⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,137⟩)),
  (⟨94,43,[9],77⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,137⟩)),
  (⟨94,43,[2],117⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,137⟩)),
  (⟨94,43,[8],163⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,137⟩)),
  (⟨94,43,[0],207⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,137⟩)),
  (⟨94,43,[3],519⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,137⟩)),
  (⟨94,43,[1],522⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,137⟩)),
  (⟨94,43,[16,18,19,20,22,23],558⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,137⟩)),
  (⟨94,43,[17,21],561⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,137⟩)),
  (⟨94,43,[32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63],633⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,137⟩)),
  (⟨94,43,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,137⟩)),
  (⟨94,43,[11],871⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,137⟩)),
  (⟨94,43,[24,26,27,28,30,31],970⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,137⟩)),
  (⟨94,43,[25,29],974⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,137⟩)),
  (⟨94,43,[4,6,7,12,14,15],1227⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,137⟩)),
  (⟨94,43,[5,13],1231⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,137⟩)),
  (⟨94,44,[-1],631⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.bound ⟨true,false,224⟩)),
  (⟨94,45,[-1],639⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,185⟩)),
  (⟨94,46,[-1],636⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.bound ⟨true,false,289⟩)),
  (⟨94,47,[-1],638⟩, ([⟨true,true,215⟩,⟨false,false,264⟩,⟨false,true,426⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.bound ⟨true,false,137⟩)),
  (⟨94,48,[-1],653⟩, ([⟨true,true,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.bound ⟨true,false,249⟩)),
  (⟨94,49,[-1],657⟩, ([⟨true,true,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,204⟩)),
  (⟨94,50,[-1],655⟩, ([⟨true,true,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,334⟩)),
  (⟨94,51,[-1],656⟩, ([⟨true,true,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,142⟩)),
  (⟨94,52,[-1],653⟩, ([⟨true,true,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.bound ⟨true,false,249⟩)),
  (⟨94,53,[-1],657⟩, ([⟨true,true,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,204⟩)),
  (⟨94,54,[-1],655⟩, ([⟨true,true,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.bound ⟨true,false,334⟩)),
  (⟨94,55,[-1],656⟩, ([⟨true,true,215⟩,⟨true,true,264⟩,⟨false,false,446⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.bound ⟨true,false,142⟩)),
  (⟨94,56,[-1],986⟩, ([⟨true,true,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,false,508⟩,⟨false,false,222⟩,⟨false,false,254⟩],.bound ⟨true,false,498⟩)),
  (⟨94,57,[-1],989⟩, ([⟨true,true,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨false,false,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,460⟩)),
  (⟨94,58,[-1],988⟩, ([⟨true,true,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,true,254⟩,⟨false,false,222⟩,⟨false,false,552⟩],.bound ⟨true,false,405⟩)),
  (⟨94,59,[-1],990⟩, ([⟨true,true,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,true,254⟩,⟨true,true,552⟩,⟨false,false,222⟩],.bound ⟨true,false,483⟩)),
  (⟨94,60,[-1],986⟩, ([⟨true,true,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,false,508⟩,⟨true,true,222⟩,⟨false,false,254⟩],.bound ⟨true,false,498⟩)),
  (⟨94,61,[-1],989⟩, ([⟨true,true,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,true,222⟩,⟨false,false,254⟩,⟨false,true,508⟩],.bound ⟨true,false,460⟩)),
  (⟨94,62,[-1],988⟩, ([⟨true,true,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨false,false,552⟩],.bound ⟨true,false,405⟩)),
  (⟨94,63,[-1],990⟩, ([⟨true,true,215⟩,⟨true,true,264⟩,⟨true,true,446⟩,⟨true,true,222⟩,⟨true,true,254⟩,⟨true,true,552⟩],.bound ⟨true,false,483⟩)),
  (⟨96,0,[-1],505⟩, ([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.bound ⟨true,false,583⟩)),
  (⟨96,1,[-1],522⟩, ([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.bound ⟨true,false,416⟩)),
  (⟨96,2,[-1],504⟩, ([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.bound ⟨true,false,376⟩)),
  (⟨96,3,[-1],504⟩, ([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.bound ⟨true,false,561⟩)),
  (⟨96,4,[-1],1203⟩, ([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,false,516⟩,⟨true,true,629⟩,⟨false,false,223⟩],.bound ⟨true,false,583⟩)),
  (⟨96,5,[-1],1231⟩, ([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.bound ⟨true,false,416⟩)),
  (⟨96,6,[-1],1202⟩, ([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,true,223⟩,⟨true,true,629⟩,⟨false,false,569⟩],.bound ⟨true,false,376⟩)),
  (⟨96,7,[-1],1202⟩, ([⟨true,false,433⟩,⟨false,false,222⟩,⟨false,false,296⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨true,true,629⟩],.bound ⟨true,false,561⟩)),
  (⟨96,8,[8,12,40,44],162⟩, ([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.bound ⟨true,false,117⟩)),
  (⟨96,8,[1,9],283⟩, ([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.bound ⟨true,false,117⟩)),
  (⟨96,8,[0],526⟩, ([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.bound ⟨true,false,117⟩)),
  (⟨96,8,[16,17,20,21,24,25,28,29],537⟩, ([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.bound ⟨true,false,117⟩)),
  (⟨96,8,[32,33,36,37,41,45,48,49,52,53,56,57,60,61],633⟩, ([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.bound ⟨true,false,117⟩)),
  (⟨96,8,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩, ([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.bound ⟨true,false,117⟩)),
  (⟨96,8,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.bound ⟨true,false,117⟩)),
  (⟨96,8,[4,5,13],1218⟩, ([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.bound ⟨true,false,117⟩)),
  (⟨96,9,[9],66⟩, ([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.bound ⟨true,false,147⟩)),
  (⟨96,9,[0,8],283⟩, ([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.bound ⟨true,false,147⟩)),
  (⟨96,9,[1],526⟩, ([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.bound ⟨true,false,147⟩)),
  (⟨96,9,[16,17,20,21,24,25,28,29],537⟩, ([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.bound ⟨true,false,147⟩)),
  (⟨96,9,[32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],633⟩, ([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.bound ⟨true,false,147⟩)),
  (⟨96,9,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31,34,35,38,39,42,43,46,47,50,51,54,55,58,59,62,63],645⟩, ([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.bound ⟨true,false,147⟩)),
  (⟨96,9,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.bound ⟨true,false,147⟩)),
  (⟨96,9,[4,5,12,13],1218⟩, ([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.bound ⟨true,false,147⟩)),
  (⟨96,10,[10,14,42,46],37⟩, ([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.bound ⟨true,false,203⟩)),
  (⟨96,10,[2],526⟩, ([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.bound ⟨true,false,203⟩)),
  (⟨96,10,[18,22,26,30],537⟩, ([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.bound ⟨true,false,203⟩)),
  (⟨96,10,[34,35,38,39,43,47,50,54,58,59,62,63],633⟩, ([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.bound ⟨true,false,203⟩)),
  (⟨96,10,[0,1,4,5,8,9,12,13,16,17,20,21,24,25,28,29,32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],645⟩, ([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.bound ⟨true,false,203⟩)),
  (⟨96,10,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.bound ⟨true,false,203⟩)),
  (⟨96,10,[3,7,11,15,19,23,27,31,51,55],863⟩, ([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.bound ⟨true,false,203⟩)),
  (⟨96,10,[6],1218⟩, ([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.bound ⟨true,false,203⟩)),
  (⟨96,11,[-1],860⟩, ([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.bound ⟨true,false,70⟩)),
  (⟨96,12,[-1],1203⟩, ([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,false,516⟩,⟨true,true,629⟩,⟨false,false,223⟩],.bound ⟨true,false,117⟩)),
  (⟨96,13,[-1],1231⟩, ([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.bound ⟨true,false,147⟩)),
  (⟨96,14,[-1],1202⟩, ([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨true,true,629⟩,⟨false,false,569⟩],.bound ⟨true,false,203⟩)),
  (⟨96,15,[-1],1202⟩, ([⟨false,false,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨true,true,629⟩],.bound ⟨true,false,70⟩)),
  (⟨96,16,[-1],543⟩, ([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.bound ⟨true,false,161⟩)),
  (⟨96,17,[-1],561⟩, ([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.bound ⟨true,false,202⟩)),
  (⟨96,18,[-1],542⟩, ([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.bound ⟨true,false,304⟩)),
  (⟨96,19,[-1],542⟩, ([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.bound ⟨true,false,74⟩)),
  (⟨96,20,[-1],543⟩, ([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨true,false,516⟩,⟨true,true,629⟩,⟨false,false,223⟩],.bound ⟨true,false,161⟩)),
  (⟨96,21,[-1],561⟩, ([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.bound ⟨true,false,202⟩)),
  (⟨96,22,[-1],542⟩, ([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨true,true,223⟩,⟨true,true,629⟩,⟨false,false,569⟩],.bound ⟨true,false,304⟩)),
  (⟨96,23,[-1],542⟩, ([⟨true,true,296⟩,⟨false,false,222⟩,⟨false,false,453⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨true,true,629⟩],.bound ⟨true,false,74⟩)),
  (⟨96,24,[-1],956⟩, ([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.bound ⟨true,false,546⟩)),
  (⟨96,25,[-1],974⟩, ([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.bound ⟨true,false,463⟩)),
  (⟨96,26,[-1],955⟩, ([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.bound ⟨true,false,429⟩)),
  (⟨96,27,[-1],955⟩, ([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.bound ⟨true,false,530⟩)),
  (⟨96,28,[-1],956⟩, ([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,false,516⟩,⟨true,true,629⟩,⟨false,false,223⟩],.bound ⟨true,false,546⟩)),
  (⟨96,29,[-1],974⟩, ([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.bound ⟨true,false,463⟩)),
  (⟨96,30,[-1],955⟩, ([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,true,223⟩,⟨true,true,629⟩,⟨false,false,569⟩],.bound ⟨true,false,429⟩)),
  (⟨96,31,[-1],955⟩, ([⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,222⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨true,true,629⟩],.bound ⟨true,false,530⟩)),
  (⟨96,32,[-1],505⟩, ([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.bound ⟨true,false,583⟩)),
  (⟨96,33,[-1],522⟩, ([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.bound ⟨true,false,416⟩)),
  (⟨96,34,[-1],509⟩, ([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.bound ⟨true,false,376⟩)),
  (⟨96,35,[-1],524⟩, ([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.bound ⟨true,false,561⟩)),
  (⟨96,36,[-1],1203⟩, ([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨true,false,516⟩,⟨true,true,629⟩,⟨false,false,223⟩],.bound ⟨true,false,583⟩)),
  (⟨96,37,[-1],1231⟩, ([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.bound ⟨true,false,416⟩)),
  (⟨96,38,[-1],1211⟩, ([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨true,true,223⟩,⟨true,true,629⟩,⟨false,false,569⟩],.bound ⟨true,false,376⟩)),
  (⟨96,39,[-1],1235⟩, ([⟨true,false,433⟩,⟨true,true,222⟩,⟨false,false,296⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨true,true,629⟩],.bound ⟨true,false,561⟩)),
  (⟨96,40,[-1],634⟩, ([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.bound ⟨true,false,117⟩)),
  (⟨96,41,[-1],640⟩, ([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.bound ⟨true,false,147⟩)),
  (⟨96,42,[10,14,42,46],37⟩, ([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.bound ⟨true,false,203⟩)),
  (⟨96,42,[34],526⟩, ([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.bound ⟨true,false,203⟩)),
  (⟨96,42,[50,54,58,62],537⟩, ([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.bound ⟨true,false,203⟩)),
  (⟨96,42,[2,3,6,7,11,15,18,22,26,27,30,31],633⟩, ([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.bound ⟨true,false,203⟩)),
  (⟨96,42,[0,1,4,5,8,9,12,13,16,17,20,21,24,25,28,29,32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],645⟩, ([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.bound ⟨true,false,203⟩)),
  (⟨96,42,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.bound ⟨true,false,203⟩)),
  (⟨96,42,[19,23,35,39,43,47,51,55,59,63],863⟩, ([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.bound ⟨true,false,203⟩)),
  (⟨96,42,[38],1218⟩, ([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.bound ⟨true,false,203⟩)),
  (⟨96,43,[43],91⟩, ([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.bound ⟨true,false,70⟩)),
  (⟨96,43,[35],526⟩, ([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.bound ⟨true,false,70⟩)),
  (⟨96,43,[51,55,59,63],537⟩, ([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.bound ⟨true,false,70⟩)),
  (⟨96,43,[2,3,6,7,10,11,14,15,18,19,22,23,26,27,30,31],633⟩, ([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.bound ⟨true,false,70⟩)),
  (⟨96,43,[0,1,4,5,8,9,12,13,16,17,20,21,24,25,28,29,32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],645⟩, ([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.bound ⟨true,false,70⟩)),
  (⟨96,43,[64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127],739⟩, ([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.bound ⟨true,false,70⟩)),
  (⟨96,43,[34,38,42,46,50,54,58,62],863⟩, ([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.bound ⟨true,false,70⟩)),
  (⟨96,43,[39,47],1218⟩, ([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.bound ⟨true,false,70⟩)),
  (⟨96,44,[-1],1203⟩, ([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,false,516⟩,⟨true,true,629⟩,⟨false,false,223⟩],.bound ⟨true,false,117⟩)),
  (⟨96,45,[-1],1231⟩, ([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.bound ⟨true,false,147⟩)),
  (⟨96,46,[-1],1211⟩, ([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨true,true,629⟩,⟨false,false,569⟩],.bound ⟨true,false,203⟩)),
  (⟨96,47,[-1],1223⟩, ([⟨true,true,222⟩,⟨false,false,296⟩,⟨false,true,433⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨true,true,629⟩],.bound ⟨true,false,70⟩)),
  (⟨96,48,[-1],543⟩, ([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.bound ⟨true,false,161⟩)),
  (⟨96,49,[-1],561⟩, ([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.bound ⟨true,false,202⟩)),
  (⟨96,50,[-1],547⟩, ([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.bound ⟨true,false,304⟩)),
  (⟨96,51,[-1],557⟩, ([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.bound ⟨true,false,74⟩)),
  (⟨96,52,[-1],543⟩, ([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,false,516⟩,⟨true,true,629⟩,⟨false,false,223⟩],.bound ⟨true,false,161⟩)),
  (⟨96,53,[-1],561⟩, ([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.bound ⟨true,false,202⟩)),
  (⟨96,54,[-1],547⟩, ([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,223⟩,⟨true,true,629⟩,⟨false,false,569⟩],.bound ⟨true,false,304⟩)),
  (⟨96,55,[-1],557⟩, ([⟨true,true,222⟩,⟨true,true,296⟩,⟨false,false,453⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨true,true,629⟩],.bound ⟨true,false,74⟩)),
  (⟨96,56,[-1],956⟩, ([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,false,516⟩,⟨false,false,223⟩,⟨false,false,629⟩],.bound ⟨true,false,546⟩)),
  (⟨96,57,[-1],974⟩, ([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨false,false,223⟩,⟨false,false,629⟩,⟨false,true,516⟩],.bound ⟨true,false,463⟩)),
  (⟨96,58,[-1],960⟩, ([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,223⟩,⟨false,false,569⟩,⟨false,false,629⟩],.bound ⟨true,false,429⟩)),
  (⟨96,59,[-1],971⟩, ([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨false,false,629⟩],.bound ⟨true,false,530⟩)),
  (⟨96,60,[-1],956⟩, ([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,false,516⟩,⟨true,true,629⟩,⟨false,false,223⟩],.bound ⟨true,false,546⟩)),
  (⟨96,61,[-1],974⟩, ([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,629⟩,⟨false,false,223⟩,⟨false,true,516⟩],.bound ⟨true,false,463⟩)),
  (⟨96,62,[-1],960⟩, ([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,223⟩,⟨true,true,629⟩,⟨false,false,569⟩],.bound ⟨true,false,429⟩)),
  (⟨96,63,[-1],971⟩, ([⟨true,true,222⟩,⟨true,true,296⟩,⟨true,true,453⟩,⟨true,true,223⟩,⟨true,true,569⟩,⟨true,true,629⟩],.bound ⟨true,false,530⟩))
]

private theorem rows_fst : readyRows.map Prod.fst = selectedRecords := by
  decide +kernel

private theorem rows_branch : ∀ x ∈ readyRows, refBranch x.1.goal x.1.branch = x.2 := by
  decide +kernel

private theorem ready_all : ∀ x ∈ readyRows, recordReady x.1 (cachedHyp x.1.goal) x.2 := by
  decide +kernel

private theorem records_valid : ∀ r ∈ selectedRecords, middleCertRecordValid middleCertData r := by
  intro r hr
  have hg := records_goals r hr
  rw [← rows_fst] at hr
  obtain ⟨x, hx, hxr⟩ := List.mem_map.mp hr
  subst hxr
  exact ready_valid x.1 (cachedHyp x.1.goal) x.2 (rows_branch x hx) (cached_ok x.1.goal hg)
    (hyp_ok x.1.goal hg) (par_ok x.1.goal hg) (ready_all x hx)

private theorem parentsLen :
    (middleCertData.parents (middleCertParity 5)).length = 128 := by
  decide +kernel

private theorem refCover_82 : ∀ j ∈ List.range (cachedBranches 83).length,
    (refBranch 83 j).2 = RefComparison.automatic ∨
    (∃ r ∈ (branchRecords_82)[j]?.getD [], r.goal = 83 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
    (5 < 9 ∧ ∀ k ∈ List.range 128,
      ∃ r ∈ (branchRecords_82)[j]?.getD [], r.goal = 83 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_82 : ∀ j ∈ List.range
      (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 83)).length,
    (middleCertBranch middleCertData (middleCertGoal middleCertData 83) j).2 = .automatic ∨
    (∃ r ∈ selectedRecords, r.goal = 83 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
    (5 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 5)).length,
      ∃ r ∈ selectedRecords, r.goal = 83 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rw [List.mem_range, branch_len 83 cached_83, ← List.mem_range] at hj
  rcases refCover_82 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · refine Or.inl ?_
    rw [branch_decode 83 j cached_83]
    simp [decodeBranch, decodeComparison, ha]
  · exact Or.inr (Or.inl ⟨r, sub_82 j r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, fun k hk => ?_⟩)
    rw [parentsLen] at hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, sub_82 j r hr, hg, hb, hp⟩

private theorem refCover_83 : ∀ j ∈ List.range (cachedBranches 84).length,
    (refBranch 84 j).2 = RefComparison.automatic ∨
    (∃ r ∈ (branchRecords_83)[j]?.getD [], r.goal = 84 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
    (5 < 9 ∧ ∀ k ∈ List.range 128,
      ∃ r ∈ (branchRecords_83)[j]?.getD [], r.goal = 84 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_83 : ∀ j ∈ List.range
      (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 84)).length,
    (middleCertBranch middleCertData (middleCertGoal middleCertData 84) j).2 = .automatic ∨
    (∃ r ∈ selectedRecords, r.goal = 84 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
    (5 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 5)).length,
      ∃ r ∈ selectedRecords, r.goal = 84 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rw [List.mem_range, branch_len 84 cached_84, ← List.mem_range] at hj
  rcases refCover_83 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · refine Or.inl ?_
    rw [branch_decode 84 j cached_84]
    simp [decodeBranch, decodeComparison, ha]
  · exact Or.inr (Or.inl ⟨r, sub_83 j r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, fun k hk => ?_⟩)
    rw [parentsLen] at hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, sub_83 j r hr, hg, hb, hp⟩

private theorem refCover_84 : ∀ j ∈ List.range (cachedBranches 85).length,
    (refBranch 85 j).2 = RefComparison.automatic ∨
    (∃ r ∈ (branchRecords_84)[j]?.getD [], r.goal = 85 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
    (5 < 9 ∧ ∀ k ∈ List.range 128,
      ∃ r ∈ (branchRecords_84)[j]?.getD [], r.goal = 85 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_84 : ∀ j ∈ List.range
      (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 85)).length,
    (middleCertBranch middleCertData (middleCertGoal middleCertData 85) j).2 = .automatic ∨
    (∃ r ∈ selectedRecords, r.goal = 85 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
    (5 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 5)).length,
      ∃ r ∈ selectedRecords, r.goal = 85 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rw [List.mem_range, branch_len 85 cached_85, ← List.mem_range] at hj
  rcases refCover_84 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · refine Or.inl ?_
    rw [branch_decode 85 j cached_85]
    simp [decodeBranch, decodeComparison, ha]
  · exact Or.inr (Or.inl ⟨r, sub_84 j r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, fun k hk => ?_⟩)
    rw [parentsLen] at hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, sub_84 j r hr, hg, hb, hp⟩

private theorem refCover_85 : ∀ j ∈ List.range (cachedBranches 86).length,
    (refBranch 86 j).2 = RefComparison.automatic ∨
    (∃ r ∈ (branchRecords_85)[j]?.getD [], r.goal = 86 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
    (5 < 9 ∧ ∀ k ∈ List.range 128,
      ∃ r ∈ (branchRecords_85)[j]?.getD [], r.goal = 86 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_85 : ∀ j ∈ List.range
      (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 86)).length,
    (middleCertBranch middleCertData (middleCertGoal middleCertData 86) j).2 = .automatic ∨
    (∃ r ∈ selectedRecords, r.goal = 86 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
    (5 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 5)).length,
      ∃ r ∈ selectedRecords, r.goal = 86 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rw [List.mem_range, branch_len 86 cached_86, ← List.mem_range] at hj
  rcases refCover_85 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · refine Or.inl ?_
    rw [branch_decode 86 j cached_86]
    simp [decodeBranch, decodeComparison, ha]
  · exact Or.inr (Or.inl ⟨r, sub_85 j r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, fun k hk => ?_⟩)
    rw [parentsLen] at hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, sub_85 j r hr, hg, hb, hp⟩

private theorem refCover_86 : ∀ j ∈ List.range (cachedBranches 87).length,
    (refBranch 87 j).2 = RefComparison.automatic ∨
    (∃ r ∈ (branchRecords_86)[j]?.getD [], r.goal = 87 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
    (5 < 9 ∧ ∀ k ∈ List.range 128,
      ∃ r ∈ (branchRecords_86)[j]?.getD [], r.goal = 87 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_86 : ∀ j ∈ List.range
      (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 87)).length,
    (middleCertBranch middleCertData (middleCertGoal middleCertData 87) j).2 = .automatic ∨
    (∃ r ∈ selectedRecords, r.goal = 87 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
    (5 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 5)).length,
      ∃ r ∈ selectedRecords, r.goal = 87 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rw [List.mem_range, branch_len 87 cached_87, ← List.mem_range] at hj
  rcases refCover_86 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · refine Or.inl ?_
    rw [branch_decode 87 j cached_87]
    simp [decodeBranch, decodeComparison, ha]
  · exact Or.inr (Or.inl ⟨r, sub_86 j r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, fun k hk => ?_⟩)
    rw [parentsLen] at hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, sub_86 j r hr, hg, hb, hp⟩

private theorem refCover_87 : ∀ j ∈ List.range (cachedBranches 88).length,
    (refBranch 88 j).2 = RefComparison.automatic ∨
    (∃ r ∈ (branchRecords_87)[j]?.getD [], r.goal = 88 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
    (5 < 9 ∧ ∀ k ∈ List.range 128,
      ∃ r ∈ (branchRecords_87)[j]?.getD [], r.goal = 88 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_87 : ∀ j ∈ List.range
      (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 88)).length,
    (middleCertBranch middleCertData (middleCertGoal middleCertData 88) j).2 = .automatic ∨
    (∃ r ∈ selectedRecords, r.goal = 88 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
    (5 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 5)).length,
      ∃ r ∈ selectedRecords, r.goal = 88 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rw [List.mem_range, branch_len 88 cached_88, ← List.mem_range] at hj
  rcases refCover_87 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · refine Or.inl ?_
    rw [branch_decode 88 j cached_88]
    simp [decodeBranch, decodeComparison, ha]
  · exact Or.inr (Or.inl ⟨r, sub_87 j r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, fun k hk => ?_⟩)
    rw [parentsLen] at hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, sub_87 j r hr, hg, hb, hp⟩

private theorem refCover_88 : ∀ j ∈ List.range (cachedBranches 89).length,
    (refBranch 89 j).2 = RefComparison.automatic ∨
    (∃ r ∈ (branchRecords_88)[j]?.getD [], r.goal = 89 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
    (5 < 9 ∧ ∀ k ∈ List.range 128,
      ∃ r ∈ (branchRecords_88)[j]?.getD [], r.goal = 89 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_88 : ∀ j ∈ List.range
      (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 89)).length,
    (middleCertBranch middleCertData (middleCertGoal middleCertData 89) j).2 = .automatic ∨
    (∃ r ∈ selectedRecords, r.goal = 89 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
    (5 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 5)).length,
      ∃ r ∈ selectedRecords, r.goal = 89 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rw [List.mem_range, branch_len 89 cached_89, ← List.mem_range] at hj
  rcases refCover_88 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · refine Or.inl ?_
    rw [branch_decode 89 j cached_89]
    simp [decodeBranch, decodeComparison, ha]
  · exact Or.inr (Or.inl ⟨r, sub_88 j r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, fun k hk => ?_⟩)
    rw [parentsLen] at hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, sub_88 j r hr, hg, hb, hp⟩

private theorem refCover_89 : ∀ j ∈ List.range (cachedBranches 90).length,
    (refBranch 90 j).2 = RefComparison.automatic ∨
    (∃ r ∈ (branchRecords_89)[j]?.getD [], r.goal = 90 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
    (5 < 9 ∧ ∀ k ∈ List.range 128,
      ∃ r ∈ (branchRecords_89)[j]?.getD [], r.goal = 90 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_89 : ∀ j ∈ List.range
      (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 90)).length,
    (middleCertBranch middleCertData (middleCertGoal middleCertData 90) j).2 = .automatic ∨
    (∃ r ∈ selectedRecords, r.goal = 90 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
    (5 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 5)).length,
      ∃ r ∈ selectedRecords, r.goal = 90 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rw [List.mem_range, branch_len 90 cached_90, ← List.mem_range] at hj
  rcases refCover_89 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · refine Or.inl ?_
    rw [branch_decode 90 j cached_90]
    simp [decodeBranch, decodeComparison, ha]
  · exact Or.inr (Or.inl ⟨r, sub_89 j r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, fun k hk => ?_⟩)
    rw [parentsLen] at hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, sub_89 j r hr, hg, hb, hp⟩

private theorem refCover_90 : ∀ j ∈ List.range (cachedBranches 91).length,
    (refBranch 91 j).2 = RefComparison.automatic ∨
    (∃ r ∈ (branchRecords_90)[j]?.getD [], r.goal = 91 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
    (5 < 9 ∧ ∀ k ∈ List.range 128,
      ∃ r ∈ (branchRecords_90)[j]?.getD [], r.goal = 91 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_90 : ∀ j ∈ List.range
      (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 91)).length,
    (middleCertBranch middleCertData (middleCertGoal middleCertData 91) j).2 = .automatic ∨
    (∃ r ∈ selectedRecords, r.goal = 91 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
    (5 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 5)).length,
      ∃ r ∈ selectedRecords, r.goal = 91 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rw [List.mem_range, branch_len 91 cached_91, ← List.mem_range] at hj
  rcases refCover_90 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · refine Or.inl ?_
    rw [branch_decode 91 j cached_91]
    simp [decodeBranch, decodeComparison, ha]
  · exact Or.inr (Or.inl ⟨r, sub_90 j r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, fun k hk => ?_⟩)
    rw [parentsLen] at hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, sub_90 j r hr, hg, hb, hp⟩

private theorem refCover_91 : ∀ j ∈ List.range (cachedBranches 92).length,
    (refBranch 92 j).2 = RefComparison.automatic ∨
    (∃ r ∈ (branchRecords_91)[j]?.getD [], r.goal = 92 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
    (5 < 9 ∧ ∀ k ∈ List.range 128,
      ∃ r ∈ (branchRecords_91)[j]?.getD [], r.goal = 92 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_91 : ∀ j ∈ List.range
      (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 92)).length,
    (middleCertBranch middleCertData (middleCertGoal middleCertData 92) j).2 = .automatic ∨
    (∃ r ∈ selectedRecords, r.goal = 92 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
    (5 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 5)).length,
      ∃ r ∈ selectedRecords, r.goal = 92 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rw [List.mem_range, branch_len 92 cached_92, ← List.mem_range] at hj
  rcases refCover_91 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · refine Or.inl ?_
    rw [branch_decode 92 j cached_92]
    simp [decodeBranch, decodeComparison, ha]
  · exact Or.inr (Or.inl ⟨r, sub_91 j r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, fun k hk => ?_⟩)
    rw [parentsLen] at hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, sub_91 j r hr, hg, hb, hp⟩

private theorem refCover_92 : ∀ j ∈ List.range (cachedBranches 93).length,
    (refBranch 93 j).2 = RefComparison.automatic ∨
    (∃ r ∈ (branchRecords_92)[j]?.getD [], r.goal = 93 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
    (5 < 9 ∧ ∀ k ∈ List.range 128,
      ∃ r ∈ (branchRecords_92)[j]?.getD [], r.goal = 93 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_92 : ∀ j ∈ List.range
      (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 93)).length,
    (middleCertBranch middleCertData (middleCertGoal middleCertData 93) j).2 = .automatic ∨
    (∃ r ∈ selectedRecords, r.goal = 93 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
    (5 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 5)).length,
      ∃ r ∈ selectedRecords, r.goal = 93 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rw [List.mem_range, branch_len 93 cached_93, ← List.mem_range] at hj
  rcases refCover_92 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · refine Or.inl ?_
    rw [branch_decode 93 j cached_93]
    simp [decodeBranch, decodeComparison, ha]
  · exact Or.inr (Or.inl ⟨r, sub_92 j r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, fun k hk => ?_⟩)
    rw [parentsLen] at hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, sub_92 j r hr, hg, hb, hp⟩

private theorem refCover_93 : ∀ j ∈ List.range (cachedBranches 94).length,
    (refBranch 94 j).2 = RefComparison.automatic ∨
    (∃ r ∈ (branchRecords_93)[j]?.getD [], r.goal = 94 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
    (5 < 9 ∧ ∀ k ∈ List.range 128,
      ∃ r ∈ (branchRecords_93)[j]?.getD [], r.goal = 94 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_93 : ∀ j ∈ List.range
      (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 94)).length,
    (middleCertBranch middleCertData (middleCertGoal middleCertData 94) j).2 = .automatic ∨
    (∃ r ∈ selectedRecords, r.goal = 94 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
    (5 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 5)).length,
      ∃ r ∈ selectedRecords, r.goal = 94 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rw [List.mem_range, branch_len 94 cached_94, ← List.mem_range] at hj
  rcases refCover_93 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · refine Or.inl ?_
    rw [branch_decode 94 j cached_94]
    simp [decodeBranch, decodeComparison, ha]
  · exact Or.inr (Or.inl ⟨r, sub_93 j r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, fun k hk => ?_⟩)
    rw [parentsLen] at hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, sub_93 j r hr, hg, hb, hp⟩

private theorem refCover_94 : ∀ j ∈ List.range (cachedBranches 95).length,
    (refBranch 95 j).2 = RefComparison.automatic ∨
    (∃ r ∈ (branchRecords_94)[j]?.getD [], r.goal = 95 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
    (5 < 9 ∧ ∀ k ∈ List.range 128,
      ∃ r ∈ (branchRecords_94)[j]?.getD [], r.goal = 95 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_94 : ∀ j ∈ List.range
      (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 95)).length,
    (middleCertBranch middleCertData (middleCertGoal middleCertData 95) j).2 = .automatic ∨
    (∃ r ∈ selectedRecords, r.goal = 95 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
    (5 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 5)).length,
      ∃ r ∈ selectedRecords, r.goal = 95 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rw [List.mem_range, branch_len 95 cached_95, ← List.mem_range] at hj
  rcases refCover_94 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · refine Or.inl ?_
    rw [branch_decode 95 j cached_95]
    simp [decodeBranch, decodeComparison, ha]
  · exact Or.inr (Or.inl ⟨r, sub_94 j r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, fun k hk => ?_⟩)
    rw [parentsLen] at hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, sub_94 j r hr, hg, hb, hp⟩

private theorem refCover_95 : ∀ j ∈ List.range (cachedBranches 96).length,
    (refBranch 96 j).2 = RefComparison.automatic ∨
    (∃ r ∈ (branchRecords_95)[j]?.getD [], r.goal = 96 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
    (5 < 9 ∧ ∀ k ∈ List.range 128,
      ∃ r ∈ (branchRecords_95)[j]?.getD [], r.goal = 96 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_95 : ∀ j ∈ List.range
      (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 96)).length,
    (middleCertBranch middleCertData (middleCertGoal middleCertData 96) j).2 = .automatic ∨
    (∃ r ∈ selectedRecords, r.goal = 96 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
    (5 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 5)).length,
      ∃ r ∈ selectedRecords, r.goal = 96 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rw [List.mem_range, branch_len 96 cached_96, ← List.mem_range] at hj
  rcases refCover_95 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · refine Or.inl ?_
    rw [branch_decode 96 j cached_96]
    simp [decodeBranch, decodeComparison, ha]
  · exact Or.inr (Or.inl ⟨r, sub_95 j r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, fun k hk => ?_⟩)
    rw [parentsLen] at hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, sub_95 j r hr, hg, hb, hp⟩

private theorem refCover_96 : ∀ j ∈ List.range (cachedBranches 97).length,
    (refBranch 97 j).2 = RefComparison.automatic ∨
    (∃ r ∈ (branchRecords_96)[j]?.getD [], r.goal = 97 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
    (5 < 9 ∧ ∀ k ∈ List.range 128,
      ∃ r ∈ (branchRecords_96)[j]?.getD [], r.goal = 97 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  decide +kernel

private theorem cover_96 : ∀ j ∈ List.range
      (middleCertGoalBranches middleCertData (middleCertGoal middleCertData 97)).length,
    (middleCertBranch middleCertData (middleCertGoal middleCertData 97) j).2 = .automatic ∨
    (∃ r ∈ selectedRecords, r.goal = 97 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
    (5 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 5)).length,
      ∃ r ∈ selectedRecords, r.goal = 97 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  intro j hj
  rw [List.mem_range, branch_len 97 cached_97, ← List.mem_range] at hj
  rcases refCover_96 j hj with ha | ⟨r, hr, hg, hb, hp⟩ | ⟨hf, hall⟩
  · refine Or.inl ?_
    rw [branch_decode 97 j cached_97]
    simp [decodeBranch, decodeComparison, ha]
  · exact Or.inr (Or.inl ⟨r, sub_96 j r hr, hg, hb, hp⟩)
  · refine Or.inr (Or.inr ⟨hf, fun k hk => ?_⟩)
    rw [parentsLen] at hk
    obtain ⟨r, hr, hg, hb, hp⟩ := hall k hk
    exact ⟨r, sub_96 j r hr, hg, hb, hp⟩

private theorem coverage :
    ∀ i ∈ selectedGoals,
      ∀ j ∈ List.range
          (middleCertGoalBranches middleCertData (middleCertGoal middleCertData (i+1))).length,
        (middleCertBranch middleCertData (middleCertGoal middleCertData (i+1)) j).2 = .automatic ∨
        (∃ r ∈ selectedRecords, r.goal = i+1 ∧ r.branch = j ∧ (-1 : ℤ) ∈ r.parents) ∨
        (5 < 9 ∧ ∀ k ∈ List.range (middleCertData.parents (middleCertParity 5)).length,
          ∃ r ∈ selectedRecords, r.goal = i+1 ∧ r.branch = j ∧ (k : ℤ) ∈ r.parents) := by
  simp only [selectedGoals, List.forall_mem_cons, List.forall_mem_nil, and_true]
  exact ⟨cover_82, cover_83, cover_84, cover_85, cover_86, cover_87, cover_88, cover_89, cover_90, cover_91, cover_92, cover_93, cover_94, cover_95, cover_96, List.forall_mem_nil _⟩

end FastFamily5

open FastFamily5

theorem solution : middleCertFamilyValid middleCertData 5 := by
  have subset : ∀ r ∈ selectedRecords, r ∈ middleCertData.records := by
    intro r hr
    rw [← records_eq] at hr
    exact (List.mem_filter.mp hr).1
  have recorded (g b : ℕ) (p : ℤ) :
      (∃ r ∈ selectedRecords, r.goal = g ∧ r.branch = b ∧ p ∈ r.parents) →
      middleCertRecorded middleCertData g b p := by
    rintro ⟨r, hr, hg, hb, hp⟩
    exact ⟨r, subset r hr, hg, hb, hp⟩
  unfold middleCertFamilyValid
  refine ⟨?_, ?_, ?_⟩
  · decide +kernel
  · intro r hr hf
    apply records_valid r
    rw [← records_eq]
    exact List.mem_filter.mpr ⟨hr, by simpa only [decide_eq_true_eq] using hf⟩
  · intro i hi hf j hj
    have himem : i ∈ selectedGoals := by
      rw [← goals_eq]
      exact List.mem_filter.mpr ⟨hi, by simpa only [decide_eq_true_eq] using hf⟩
    rcases coverage i himem j hj with ha | hn | ⟨hf9, hp⟩
    · exact Or.inl ha
    · exact Or.inr (Or.inl (recorded _ _ _ hn))
    · exact Or.inr (Or.inr ⟨hf9, fun k hk => recorded _ _ _ (hp k hk)⟩)

#print axioms solution
