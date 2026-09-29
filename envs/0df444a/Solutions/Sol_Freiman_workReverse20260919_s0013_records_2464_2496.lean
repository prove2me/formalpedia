-- Prove2me | solution 1 for Freiman.workReverse20260919_s0013_records_2464_2496
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T09:25:40.14667+00:00
-- url     : https://prove2.me/submissions/92ca10a6-29ac-4bcb-b3b0-0712599ea9ca

import Definitions.Def_Freiman_section14Data
import Definitions.Def_Freiman_section14Model
import Mathlib.Data.Fintype.Pi

open Freiman
set_option synthInstance.maxSize 100000
set_option maxRecDepth 100000
namespace M7Section14Sep18
instance (r : CertRectangle) : Decidable (certRectangleValid r) := by
  unfold certRectangleValid
  infer_instance
instance (t : CertThreshold) : Decidable (certThresholdDataValid t) := by
  unfold certThresholdDataValid
  infer_instance
instance (z : CertField) (q : ℚ) : Decidable (certCoefficientBoundValid z q) := by
  unfold certCoefficientBoundValid
  infer_instance
instance (w : CertWitness) : Decidable (certWitnessValid w) := by
  unfold certWitnessValid
  infer_instance
instance (C : Section14Catalog) (S : Section14State) (caseId : ℕ)
    (gs : ℕ × Section14Spec) : Decidable (section14SpecValid C S caseId gs) := by
  unfold section14SpecValid
  infer_instance
instance (C : Section14Catalog) (S : Section14State) (p : Section14Plan) :
    Decidable (section14PlanValid C S p) := by
  unfold section14PlanValid
  infer_instance
instance (outer inner : CertRectangle) : Decidable (section14RectangleContains outer inner) := by
  unfold section14RectangleContains
  infer_instance
instance (C : Section14Catalog) (si : ℕ) (r : Section14Record) :
    Decidable (section14RecordValid C si r) := by
  unfold section14RecordValid
  infer_instance
instance (C : Section14Catalog) (si parent goal : ℕ) (branch : ℤ) :
    Decidable (section14Recorded C si parent goal branch) := by
  unfold section14Recorded
  infer_instance
instance (C : Section14Catalog) (si : ℕ) : Decidable (section14Coverage C si) := by
  unfold section14Coverage
  infer_instance
instance (C : Section14Catalog) (si : ℕ) : Decidable (section14StateValid C si) := by
  unfold section14StateValid
  infer_instance
end M7Section14Sep18

open Freiman
set_option maxRecDepth 100000
set_option synthInstance.maxSize 100000
set_option Elab.async false
namespace M7Section14Sep18

def RecordDataValid (C : Section14Catalog) (si : ℕ) (r : Section14Record) : Prop :=
  let S := section14State C si
  let p := section14Proof C r.proofId
  0 < r.goal ∧ r.goal ≤ C.goals.length ∧ 0 < r.proofId ∧ r.proofId ≤ C.proofs.length ∧
  (section14Branch C (section14Goal C r.goal) r.branch).2 ≠ .automatic ∧
  (∀ b ∈ section14Parents C S, b.branch ∈ r.parents →
    section14Bound C p.lowerBound ∈ section14RecordConditions C r b ∧
    section14Bound C p.upperBound ∈ section14RecordConditions C r b) ∧
  ∃ a ∈ C.assignments, a.proofId = r.proofId ∧ si ∈ a.states ∧
    0 < a.witnessId ∧ a.witnessId ≤ C.witnesses.length ∧
    let w := section14Witness C a.witnessId
    w.firstThreshold = p.lowerBound.threshold ∧ w.secondThreshold = p.upperBound.threshold ∧
    section14RectangleContains w.rectangle S.rectangle

instance (C : Section14Catalog) (si : ℕ) (r : Section14Record) :
    Decidable (RecordDataValid C si r) := by
  unfold RecordDataValid
  infer_instance

theorem recordValid_of_data (C : Section14Catalog) (si : ℕ) (r : Section14Record)
    (hnum : ∀ a ∈ C.assignments, certWitnessValid
      (section14PairWitness C (section14Proof C a.proofId) (section14Witness C a.witnessId)))
    (h : RecordDataValid C si r) : section14RecordValid C si r := by
  rcases h with ⟨hg0,hg1,hp0,hp1,hbranch,hconditions,a,ha,hp,hs,hw0,hw1,hl,hu,hrect⟩
  have hv := hnum a ha
  rw [hp] at hv
  exact ⟨hg0,hg1,hp0,hp1,hbranch,hconditions,a,ha,hp,hs,hw0,hw1,hl,hu,hrect,hv⟩

theorem recordValid_all_of_data (C : Section14Catalog) (si : ℕ)
    (hnum : ∀ a ∈ C.assignments, certWitnessValid
      (section14PairWitness C (section14Proof C a.proofId) (section14Witness C a.witnessId)))
    (h : ∀ r ∈ C.records, si ∈ r.states → RecordDataValid C si r) :
    ∀ r ∈ C.records, si ∈ r.states → section14RecordValid C si r := by
  intro r hr hs
  exact recordValid_of_data C si r hnum (h r hr hs)
end M7Section14Sep18

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_2464_2496
private theorem valid2464 : RecordDataValid section14Catalog 13 (⟨221,(20),[1,2,5,6,13,14],[170],522⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨522,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],523⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2465 : RecordDataValid section14Catalog 13 (⟨221,(21),[1,2,5,6,13,14],[170],522⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨522,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],523⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2466 : RecordDataValid section14Catalog 13 (⟨221,(22),[1,2,5,6,13,14],[170],522⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨522,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],523⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2467 : RecordDataValid section14Catalog 13 (⟨221,(23),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2468 : RecordDataValid section14Catalog 13 (⟨221,(24),[1,2,5,6,13,14],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2469 : RecordDataValid section14Catalog 13 (⟨222,(0),[1,2,6,13,14],[170],735⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨735,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],736⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2470 : RecordDataValid section14Catalog 13 (⟨222,(1),[1,2,5,6,13,14],[170],736⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨736,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],737⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2471 : RecordDataValid section14Catalog 13 (⟨222,(2),[1,2,5,6,13,14],[170],737⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨737,[1,2,3,4,5,6,7,10,11,13,14,15,16],738⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2472 : RecordDataValid section14Catalog 13 (⟨222,(3),[1,2,5,6,13,14],[170],736⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨736,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],737⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2473 : RecordDataValid section14Catalog 13 (⟨222,(4),[1,2,5,6,13,14],[170],525⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨525,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],526⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2474 : RecordDataValid section14Catalog 13 (⟨222,(5),[1,2,5,6,13,14],[170],735⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨735,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],736⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2475 : RecordDataValid section14Catalog 13 (⟨222,(6),[1,2,6,13,14],[170],738⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨738,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],739⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2476 : RecordDataValid section14Catalog 13 (⟨222,(7),[1,2,5,6,13,14],[170],739⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨739,[1,2,3,4,5,6,7,10,11,13,14,15,16],740⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2477 : RecordDataValid section14Catalog 13 (⟨222,(8),[1,2,5,6,13,14],[170],740⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨740,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],741⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2478 : RecordDataValid section14Catalog 13 (⟨222,(9),[1,2,5,6,13,14],[170],528⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨528,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],529⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2479 : RecordDataValid section14Catalog 13 (⟨222,(10),[1,2,6,13,14],[170],741⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨741,[1,2,3,6,7,10,11,13,14,15],742⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2480 : RecordDataValid section14Catalog 13 (⟨222,(11),[1,2,6,13,14],[170],742⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨742,[1,2,3,6,7,10,11,13,14,15],743⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2481 : RecordDataValid section14Catalog 13 (⟨222,(12),[1,2,6,13,14],[170],743⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨743,[1,2,3,6,7,11,13,14,15],744⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2482 : RecordDataValid section14Catalog 13 (⟨222,(13),[1,2,6,13,14],[170],744⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨744,[1,2,3,6,7,10,11,13,14,15],745⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2483 : RecordDataValid section14Catalog 13 (⟨222,(14),[1,2,5,6,13,14],[170],531⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨531,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],532⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2484 : RecordDataValid section14Catalog 13 (⟨222,(15),[1,2,5,6,13,14],[170],735⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨735,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],736⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2485 : RecordDataValid section14Catalog 13 (⟨222,(16),[1,2,5,6,13,14],[170],738⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨738,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],739⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2486 : RecordDataValid section14Catalog 13 (⟨222,(17),[1,2,5,6,13,14],[170],745⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨745,[1,2,3,4,5,6,7,10,11,13,14,15,16],746⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2487 : RecordDataValid section14Catalog 13 (⟨222,(18),[1,2,5,6,13,14],[170],746⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨746,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],747⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2488 : RecordDataValid section14Catalog 13 (⟨222,(19),[1,2,5,6,13,14],[170],534⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨534,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],535⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2489 : RecordDataValid section14Catalog 13 (⟨222,(20),[1,2,5,6,13,14],[170],535⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨535,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],536⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2490 : RecordDataValid section14Catalog 13 (⟨222,(21),[1,2,5,6,13,14],[170],536⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨536,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],537⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2491 : RecordDataValid section14Catalog 13 (⟨222,(22),[1,2,5,6,13,14],[170],537⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨537,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2492 : RecordDataValid section14Catalog 13 (⟨222,(23),[1,2,5,6,13,14],[170],538⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨538,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],539⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2493 : RecordDataValid section14Catalog 13 (⟨222,(24),[1,2,5,6,13,14],[170],537⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨537,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2494 : RecordDataValid section14Catalog 13 (⟨224,(0),[1,2,5,6,13,14],[170],539⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨539,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],540⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2495 : RecordDataValid section14Catalog 13 (⟨224,(1),[1,2,5,6,13,14],[170],539⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨539,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],540⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2464).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2464).take 32 = [⟨221,(20),[1,2,5,6,13,14],[170],522⟩,⟨221,(21),[1,2,5,6,13,14],[170],522⟩,⟨221,(22),[1,2,5,6,13,14],[170],522⟩,⟨221,(23),[1,2,5,6,13,14],[170],517⟩,⟨221,(24),[1,2,5,6,13,14],[170],518⟩,⟨222,(0),[1,2,6,13,14],[170],735⟩,⟨222,(1),[1,2,5,6,13,14],[170],736⟩,⟨222,(2),[1,2,5,6,13,14],[170],737⟩,⟨222,(3),[1,2,5,6,13,14],[170],736⟩,⟨222,(4),[1,2,5,6,13,14],[170],525⟩,⟨222,(5),[1,2,5,6,13,14],[170],735⟩,⟨222,(6),[1,2,6,13,14],[170],738⟩,⟨222,(7),[1,2,5,6,13,14],[170],739⟩,⟨222,(8),[1,2,5,6,13,14],[170],740⟩,⟨222,(9),[1,2,5,6,13,14],[170],528⟩,⟨222,(10),[1,2,6,13,14],[170],741⟩,⟨222,(11),[1,2,6,13,14],[170],742⟩,⟨222,(12),[1,2,6,13,14],[170],743⟩,⟨222,(13),[1,2,6,13,14],[170],744⟩,⟨222,(14),[1,2,5,6,13,14],[170],531⟩,⟨222,(15),[1,2,5,6,13,14],[170],735⟩,⟨222,(16),[1,2,5,6,13,14],[170],738⟩,⟨222,(17),[1,2,5,6,13,14],[170],745⟩,⟨222,(18),[1,2,5,6,13,14],[170],746⟩,⟨222,(19),[1,2,5,6,13,14],[170],534⟩,⟨222,(20),[1,2,5,6,13,14],[170],535⟩,⟨222,(21),[1,2,5,6,13,14],[170],536⟩,⟨222,(22),[1,2,5,6,13,14],[170],537⟩,⟨222,(23),[1,2,5,6,13,14],[170],538⟩,⟨222,(24),[1,2,5,6,13,14],[170],537⟩,⟨224,(0),[1,2,5,6,13,14],[170],539⟩,⟨224,(1),[1,2,5,6,13,14],[170],539⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2464
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2465
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2466
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2467
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2468
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2469
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2470
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2471
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2472
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2473
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2474
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2475
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2476
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2477
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2478
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2479
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2480
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2481
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2482
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2483
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2484
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2485
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2486
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2487
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2488
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2489
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2490
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2491
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2492
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2493
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2494
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2495
end Section14Records_13_2464_2496

#print axioms solution
