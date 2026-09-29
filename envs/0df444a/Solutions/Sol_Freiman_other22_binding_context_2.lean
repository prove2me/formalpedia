-- Prove2me | solution 1 for Freiman.other22_binding_context_2
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T11:02:18.618792+00:00
-- url     : https://prove2.me/submissions/5fb15a8b-b410-485a-a167-8191c9b5f180

-- Array-chain equivalence is adapted with attribution from Marac submission 93a6c511-3ed0-48c3-bbd0-ecae49532be4.
import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
open Freiman
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

private def chainGet? {α : Type} : List (Array α) → ℕ → Option α
  | [], _ => none
  | A::As, j => if j < A.size then A[j]? else chainGet? As (j - A.size)

private theorem foldl_append_getElem? {α : Type} :
    ∀ (arrs : List (Array α)) (init : Array α) (i : ℕ),
      (arrs.foldl (·++·) init)[i]? =
        if i < init.size then init[i]? else chainGet? arrs (i - init.size)
  | [], init, i => by
      by_cases h : i < init.size
      · simp [h]
      · simp [h, chainGet?]
  | A::As, init, i => by
      rw [List.foldl_cons, foldl_append_getElem? As (init++A) i, Array.size_append]
      by_cases h1 : i < init.size
      · rw [if_pos h1, if_pos (by omega : i < init.size + A.size),
          Array.getElem?_append_left h1]
      · rw [if_neg h1]
        rw [show chainGet? (A::As) (i-init.size) =
              if i - init.size < A.size then A[i-init.size]? else chainGet? As (i - init.size - A.size)
            from rfl]
        by_cases h2 : i < init.size + A.size
        · rw [if_pos h2, Array.getElem?_append_right (by omega),
            if_pos (by omega : i - init.size < A.size)]
        · rw [if_neg h2, if_neg (show ¬ i - init.size < A.size by omega),
            show i - (init.size + A.size) = i - init.size - A.size by omega]

private def scoutOtherWitness (id : ℕ) : CertWitness :=
  (if id-1 < other22Witnesses01.size then other22Witnesses01[id-1]?
   else chainGet? [other22Witnesses02,other22Witnesses03,other22Witnesses04]
      (id-1-other22Witnesses01.size)).getD
    ⟨lowerHistoryZero,lowerHistoryHN,⟨0,1,0,1⟩,fun _ _ => ⟨0,0,0,0⟩,fun _ _ => 0⟩

private theorem scoutOtherWitness_eq (id : ℕ) : other22Witness id = scoutOtherWitness id := by
  have hdata : other22Witnesses = List.foldl (·++·) other22Witnesses01
      [other22Witnesses02,other22Witnesses03,other22Witnesses04] := rfl
  unfold other22Witness scoutOtherWitness
  rw [hdata,foldl_append_getElem?]


private def scoutSource : List (List CertBound) := [[10, 19, 4, 14, 1, 21, 2, 35, 11, 15, 6, 17, 23, 36], [10, 19, 4, 14, 1, 21, 2, 5, 24, 11, 15, 6, 17, 23, 36]].map (List.map other22Bound)

private def scoutEndpoints : List (List CertBound × LowerHistoryComparison) := [
  ([18, 34, 22, 37].map other22Bound, .bound (lowerHistoryComplement (other22Bound 26))),
  ([18, 34, 22, 8].map other22Bound, .bound (lowerHistoryComplement (other22Bound 25))),
  ([18, 34, 9, 13].map other22Bound, .bound (lowerHistoryComplement (other22Bound 26))),
  ([18, 34, 9, 20].map other22Bound, .bound (lowerHistoryComplement (other22Bound 27))),
  ([18, 3, 22, 37].map other22Bound, .bound (lowerHistoryComplement (other22Bound 40))),
  ([18, 3, 22, 8].map other22Bound, .bound (lowerHistoryComplement (other22Bound 38))),
  ([18, 3, 9, 13].map other22Bound, .bound (lowerHistoryComplement (other22Bound 40))),
  ([18, 3, 9, 20].map other22Bound, .bound (lowerHistoryComplement (other22Bound 39))),
  ([7, 12, 22, 37].map other22Bound, .bound (lowerHistoryComplement (other22Bound 26))),
  ([7, 12, 22, 8].map other22Bound, .bound (lowerHistoryComplement (other22Bound 25))),
  ([7, 12, 9, 13].map other22Bound, .bound (lowerHistoryComplement (other22Bound 26))),
  ([7, 12, 9, 20].map other22Bound, .bound (lowerHistoryComplement (other22Bound 27))),
  ([7, 16, 22, 37].map other22Bound, .bound (lowerHistoryComplement (other22Bound 29))),
  ([7, 16, 22, 8].map other22Bound, .bound (lowerHistoryComplement (other22Bound 28))),
  ([7, 16, 9, 13].map other22Bound, .bound (lowerHistoryComplement (other22Bound 29))),
  ([7, 16, 9, 20].map other22Bound, .bound (lowerHistoryComplement (other22Bound 30)))
]

private def scoutOtherResidual (ai : ℕ) (bi : ℤ) : List CertBound :=
  let cs := scoutSource[ai]?.getD []
  if bi < 0 then cs else
    let comp := scoutEndpoints[bi.toNat]?.getD ([],.automatic)
    (cs ++ comp.1 ++ (match comp.2 with
      | .bound b => [lowerHistoryComplement b]
      | _ => [])).eraseDups
private def scoutOtherRecordBinding (r : Other22Record) : Prop :=
  0 < r.witness ∧ r.witness ≤ 92 ∧
  (other22RecordPremise r).toFinset =
    (scoutOtherResidual r.alternative (r.branch : ℤ)).toFinset ∧
  (scoutOtherWitness r.witness).lowerBound ∈ other22RecordPremise r ∧
  (scoutOtherWitness r.witness).upperBound ∈ other22RecordPremise r ∧
  (scoutOtherWitness r.witness).rectangle = (other22Paths r.caseId).rectangle

private theorem hSource : lowerHistorySourcePremises (other22Paths 1) = scoutSource := by
  decide +kernel
private theorem hEndpoints : lowerHistoryEndpointComparisons (other22Paths 1) = scoutEndpoints := by
  decide +kernel
private theorem hResidual (ai : ℕ) (bi : ℤ) :
    lowerHistoryResidual (other22Paths 1) ai bi = scoutOtherResidual ai bi := by
  unfold lowerHistoryResidual scoutOtherResidual
  rw [hSource,hEndpoints]
  rfl
private theorem hRecord (r : Other22Record) (hk : r.caseId = 1)
    (h : scoutOtherRecordBinding r) : other22RecordBinding r := by
  unfold scoutOtherRecordBinding at h
  unfold other22RecordBinding
  simp only [scoutOtherWitness_eq,hk,hResidual] at *
  exact h

theorem solution : other22CaseBinding 1 := by
  refine ⟨?_,?_⟩
  · have hfast : ∀ r ∈ other22Records, r.caseId = 1 → scoutOtherRecordBinding r := by
      unfold scoutOtherRecordBinding
      decide +kernel
    intro r hr hk
    exact hRecord r hk (hfast r hr hk)
  · have key : ∀ ai < scoutSource.length,
        ∀ bi < scoutEndpoints.length,
          ∃ r ∈ other22Records, r.caseId = 1 ∧ r.alternative = ai ∧ r.branch = bi := by
      decide +kernel
    intro ai hai bi cs g hbi
    rw [hSource] at hai
    rw [hEndpoints] at hbi
    exact (List.getElem_of_getElem? hbi).elim fun hlt _ => key ai hai bi hlt
#print axioms solution
