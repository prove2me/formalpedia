-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_1408_1536
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:50:03.576103+00:00
-- url     : https://prove2.me/submissions/6155b181-1adf-4777-9dfa-a047329fc72c

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1408_1440
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_1408_1440
private theorem valid1408 : RecordDataValid section14Catalog 6 (⟨67,(24),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1409 : RecordDataValid section14Catalog 6 (⟨69,(0),[1,2,5,6],[150],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1410 : RecordDataValid section14Catalog 6 (⟨69,(0),[1,2,5,6,13,14],[190],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1411 : RecordDataValid section14Catalog 6 (⟨69,(1),[1,2,5,6],[150],190⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨190,[1,2,3,4,5,6,7,13,14,15,16],190⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1412 : RecordDataValid section14Catalog 6 (⟨69,(1),[1,2,5,6,13,14],[190],260⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨260,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],261⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1413 : RecordDataValid section14Catalog 6 (⟨69,(2),[1,2,5,6],[150],191⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨191,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],191⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1414 : RecordDataValid section14Catalog 6 (⟨69,(2),[1,5,6,13],[190],375⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨375,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],376⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1415 : RecordDataValid section14Catalog 6 (⟨69,(3),[1,2,5,6],[150],192⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨192,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],192⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1416 : RecordDataValid section14Catalog 6 (⟨69,(3),[1,5,6,13],[190],376⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨376,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],377⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1417 : RecordDataValid section14Catalog 6 (⟨69,(4),[1,2,5,6],[150],193⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨193,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],193⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1418 : RecordDataValid section14Catalog 6 (⟨69,(4),[1,5,6,13],[190],377⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨377,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],378⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1419 : RecordDataValid section14Catalog 6 (⟨69,(5),[1,2,5,6],[150],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1420 : RecordDataValid section14Catalog 6 (⟨69,(5),[1,2,5,6,13,14],[190],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1421 : RecordDataValid section14Catalog 6 (⟨69,(6),[1,2,5,6],[150],190⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨190,[1,2,3,4,5,6,7,13,14,15,16],190⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1422 : RecordDataValid section14Catalog 6 (⟨69,(6),[1,2,5,6,13,14],[190],260⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨260,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],261⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1423 : RecordDataValid section14Catalog 6 (⟨69,(7),[1,2,5,6],[150],191⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨191,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],191⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1424 : RecordDataValid section14Catalog 6 (⟨69,(7),[1,2,5,6,13,14],[190],375⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨375,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],376⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1425 : RecordDataValid section14Catalog 6 (⟨69,(8),[1,2,5,6],[150],192⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨192,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],192⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1426 : RecordDataValid section14Catalog 6 (⟨69,(8),[1,2,5,6,13,14],[190],376⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨376,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],377⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1427 : RecordDataValid section14Catalog 6 (⟨69,(9),[1,2,5,6],[150],193⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨193,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],193⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1428 : RecordDataValid section14Catalog 6 (⟨69,(9),[1,2,5,6,13,14],[190],377⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨377,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],378⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1429 : RecordDataValid section14Catalog 6 (⟨69,(10),[1,2,5,6],[150],194⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨194,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],194⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1430 : RecordDataValid section14Catalog 6 (⟨69,(10),[1,2,5,6,13,14],[190],194⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨194,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],194⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1431 : RecordDataValid section14Catalog 6 (⟨69,(11),[1,2,5,6],[150],195⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨195,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],195⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1432 : RecordDataValid section14Catalog 6 (⟨69,(11),[1,2,5,6,13,14],[190],267⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨267,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],268⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1433 : RecordDataValid section14Catalog 6 (⟨69,(12),[1,2,5,6],[150],195⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨195,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],195⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1434 : RecordDataValid section14Catalog 6 (⟨69,(12),[1,2,5,6,13,14],[190],378⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨378,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],379⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1435 : RecordDataValid section14Catalog 6 (⟨69,(13),[1,2,5,6],[150],195⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨195,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],195⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1436 : RecordDataValid section14Catalog 6 (⟨69,(13),[1,2,5,6,13,14],[190],378⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨378,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],379⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1437 : RecordDataValid section14Catalog 6 (⟨69,(14),[1,2,5,6],[150],193⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨193,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],193⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1438 : RecordDataValid section14Catalog 6 (⟨69,(14),[1,2,5,6,13,14],[190],377⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨377,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],378⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1439 : RecordDataValid section14Catalog 6 (⟨69,(15),[1,2,5,6],[150],196⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨196,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],196⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_1408_1440 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1408).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1408).take 32 = [⟨67,(24),[1,2,5,6,13,14],[190],2⟩,⟨69,(0),[1,2,5,6],[150],189⟩,⟨69,(0),[1,2,5,6,13,14],[190],189⟩,⟨69,(1),[1,2,5,6],[150],190⟩,⟨69,(1),[1,2,5,6,13,14],[190],260⟩,⟨69,(2),[1,2,5,6],[150],191⟩,⟨69,(2),[1,5,6,13],[190],375⟩,⟨69,(3),[1,2,5,6],[150],192⟩,⟨69,(3),[1,5,6,13],[190],376⟩,⟨69,(4),[1,2,5,6],[150],193⟩,⟨69,(4),[1,5,6,13],[190],377⟩,⟨69,(5),[1,2,5,6],[150],189⟩,⟨69,(5),[1,2,5,6,13,14],[190],189⟩,⟨69,(6),[1,2,5,6],[150],190⟩,⟨69,(6),[1,2,5,6,13,14],[190],260⟩,⟨69,(7),[1,2,5,6],[150],191⟩,⟨69,(7),[1,2,5,6,13,14],[190],375⟩,⟨69,(8),[1,2,5,6],[150],192⟩,⟨69,(8),[1,2,5,6,13,14],[190],376⟩,⟨69,(9),[1,2,5,6],[150],193⟩,⟨69,(9),[1,2,5,6,13,14],[190],377⟩,⟨69,(10),[1,2,5,6],[150],194⟩,⟨69,(10),[1,2,5,6,13,14],[190],194⟩,⟨69,(11),[1,2,5,6],[150],195⟩,⟨69,(11),[1,2,5,6,13,14],[190],267⟩,⟨69,(12),[1,2,5,6],[150],195⟩,⟨69,(12),[1,2,5,6,13,14],[190],378⟩,⟨69,(13),[1,2,5,6],[150],195⟩,⟨69,(13),[1,2,5,6,13,14],[190],378⟩,⟨69,(14),[1,2,5,6],[150],193⟩,⟨69,(14),[1,2,5,6,13,14],[190],377⟩,⟨69,(15),[1,2,5,6],[150],196⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1408
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1409
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1410
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1411
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1412
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1413
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1414
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1415
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1416
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1417
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1418
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1419
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1420
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1421
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1422
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1423
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1424
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1425
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1426
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1427
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1428
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1429
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1430
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1431
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1432
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1433
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1434
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1435
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1436
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1437
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1438
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1439
end Section14Records_6_1408_1440

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1408_1440


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1440_1472
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_1440_1472
private theorem valid1440 : RecordDataValid section14Catalog 6 (⟨69,(15),[1,2,5,6,13,14],[190],196⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨196,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],196⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1441 : RecordDataValid section14Catalog 6 (⟨69,(16),[1,2,5,6],[150],197⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨197,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],197⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1442 : RecordDataValid section14Catalog 6 (⟨69,(16),[1,2,5,6,13,14],[190],269⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨269,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],270⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1443 : RecordDataValid section14Catalog 6 (⟨69,(17),[1,2,5,6],[150],197⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨197,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],197⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1444 : RecordDataValid section14Catalog 6 (⟨69,(17),[1,2,5,6,13,14],[190],379⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨379,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],380⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1445 : RecordDataValid section14Catalog 6 (⟨69,(18),[1,2,5,6],[150],197⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨197,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],197⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1446 : RecordDataValid section14Catalog 6 (⟨69,(18),[1,2,5,6,13,14],[190],379⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨379,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],380⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1447 : RecordDataValid section14Catalog 6 (⟨69,(19),[1,2,5,6],[150],197⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨197,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],197⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1448 : RecordDataValid section14Catalog 6 (⟨69,(19),[1,2,5,6,13,14],[190],379⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨379,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],380⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1449 : RecordDataValid section14Catalog 6 (⟨69,(20),[1,2,5,6],[150],198⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨198,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],198⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1450 : RecordDataValid section14Catalog 6 (⟨69,(20),[1,2,5,6,13,14],[190],198⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨198,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],198⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1451 : RecordDataValid section14Catalog 6 (⟨69,(21),[1,2,5,6],[150],199⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨199,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],199⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1452 : RecordDataValid section14Catalog 6 (⟨69,(21),[1,2,5,6,13,14],[190],271⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨271,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],272⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1453 : RecordDataValid section14Catalog 6 (⟨69,(22),[1,2,5,6],[150],199⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨199,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],199⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1454 : RecordDataValid section14Catalog 6 (⟨69,(22),[1,2,5,6,13,14],[190],380⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨380,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],381⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1455 : RecordDataValid section14Catalog 6 (⟨69,(23),[1,2,5,6],[150],199⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨199,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],199⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1456 : RecordDataValid section14Catalog 6 (⟨69,(23),[1,2,5,6,13,14],[190],380⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨380,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],381⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1457 : RecordDataValid section14Catalog 6 (⟨69,(24),[1,2,5,6],[150],199⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨199,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],199⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1458 : RecordDataValid section14Catalog 6 (⟨69,(24),[1,2,5,6,13,14],[190],380⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨380,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],381⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1459 : RecordDataValid section14Catalog 6 (⟨72,(0),[1,2,5,6],[150],354⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨354,[1,2,4,5,6,8,9,10,12],355⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1460 : RecordDataValid section14Catalog 6 (⟨72,(0),[5,6],[190],1399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1399,[5,6,8,9,10,12],1404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1461 : RecordDataValid section14Catalog 6 (⟨72,(1),[1,2,5,6],[150],355⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨355,[1,2,4,5,6,8,9,10,12],356⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1462 : RecordDataValid section14Catalog 6 (⟨72,(1),[5,6],[190],1400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1400,[5,6,8,9,10,12],1405⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1463 : RecordDataValid section14Catalog 6 (⟨72,(2),[1,2,5,6],[150],356⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨356,[1,2,4,5,6,8,9,10,12],357⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1464 : RecordDataValid section14Catalog 6 (⟨72,(2),[5,6],[190],1401⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1401,[5,6,8,9,10,12],1406⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1465 : RecordDataValid section14Catalog 6 (⟨72,(3),[1,2,5,6],[150],357⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨357,[1,2,4,5,6,8,9,10,12],358⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1466 : RecordDataValid section14Catalog 6 (⟨72,(3),[5,6],[190],1402⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1402,[5,6,8,9,10,12],1407⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1467 : RecordDataValid section14Catalog 6 (⟨72,(4),[1,2,5,6],[150],354⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨354,[1,2,4,5,6,8,9,10,12],355⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1468 : RecordDataValid section14Catalog 6 (⟨72,(4),[5,6],[190],1399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1399,[5,6,8,9,10,12],1404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1469 : RecordDataValid section14Catalog 6 (⟨72,(5),[1,2,5,6],[150],355⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨355,[1,2,4,5,6,8,9,10,12],356⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1470 : RecordDataValid section14Catalog 6 (⟨72,(5),[5,6],[190],1400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1400,[5,6,8,9,10,12],1405⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1471 : RecordDataValid section14Catalog 6 (⟨72,(6),[1,2,5,6],[150],358⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨358,[1,2,4,5,6,8,9,10,12],359⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_1440_1472 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1440).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1440).take 32 = [⟨69,(15),[1,2,5,6,13,14],[190],196⟩,⟨69,(16),[1,2,5,6],[150],197⟩,⟨69,(16),[1,2,5,6,13,14],[190],269⟩,⟨69,(17),[1,2,5,6],[150],197⟩,⟨69,(17),[1,2,5,6,13,14],[190],379⟩,⟨69,(18),[1,2,5,6],[150],197⟩,⟨69,(18),[1,2,5,6,13,14],[190],379⟩,⟨69,(19),[1,2,5,6],[150],197⟩,⟨69,(19),[1,2,5,6,13,14],[190],379⟩,⟨69,(20),[1,2,5,6],[150],198⟩,⟨69,(20),[1,2,5,6,13,14],[190],198⟩,⟨69,(21),[1,2,5,6],[150],199⟩,⟨69,(21),[1,2,5,6,13,14],[190],271⟩,⟨69,(22),[1,2,5,6],[150],199⟩,⟨69,(22),[1,2,5,6,13,14],[190],380⟩,⟨69,(23),[1,2,5,6],[150],199⟩,⟨69,(23),[1,2,5,6,13,14],[190],380⟩,⟨69,(24),[1,2,5,6],[150],199⟩,⟨69,(24),[1,2,5,6,13,14],[190],380⟩,⟨72,(0),[1,2,5,6],[150],354⟩,⟨72,(0),[5,6],[190],1399⟩,⟨72,(1),[1,2,5,6],[150],355⟩,⟨72,(1),[5,6],[190],1400⟩,⟨72,(2),[1,2,5,6],[150],356⟩,⟨72,(2),[5,6],[190],1401⟩,⟨72,(3),[1,2,5,6],[150],357⟩,⟨72,(3),[5,6],[190],1402⟩,⟨72,(4),[1,2,5,6],[150],354⟩,⟨72,(4),[5,6],[190],1399⟩,⟨72,(5),[1,2,5,6],[150],355⟩,⟨72,(5),[5,6],[190],1400⟩,⟨72,(6),[1,2,5,6],[150],358⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1440
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1441
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1442
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1443
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1444
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1445
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1446
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1447
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1448
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1449
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1450
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1451
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1452
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1453
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1454
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1455
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1456
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1457
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1458
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1459
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1460
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1461
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1462
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1463
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1464
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1465
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1466
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1467
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1468
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1469
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1470
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1471
end Section14Records_6_1440_1472

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1440_1472


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1472_1504
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_1472_1504
private theorem valid1472 : RecordDataValid section14Catalog 6 (⟨72,(6),[5,6],[190],1403⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1403,[5,6,8,9,10,12],1408⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1473 : RecordDataValid section14Catalog 6 (⟨72,(7),[1,2,5,6],[150],357⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨357,[1,2,4,5,6,8,9,10,12],358⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1474 : RecordDataValid section14Catalog 6 (⟨72,(7),[5,6],[190],1402⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1402,[5,6,8,9,10,12],1407⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1475 : RecordDataValid section14Catalog 6 (⟨72,(8),[1,2,5,6],[150],354⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨354,[1,2,4,5,6,8,9,10,12],355⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1476 : RecordDataValid section14Catalog 6 (⟨72,(8),[5,6],[190],1399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1399,[5,6,8,9,10,12],1404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1477 : RecordDataValid section14Catalog 6 (⟨72,(9),[1,2,5,6],[150],355⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨355,[1,2,4,5,6,8,9,10,12],356⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1478 : RecordDataValid section14Catalog 6 (⟨72,(9),[5,6],[190],1400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1400,[5,6,8,9,10,12],1405⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1479 : RecordDataValid section14Catalog 6 (⟨72,(10),[1,2,5,6],[150],356⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨356,[1,2,4,5,6,8,9,10,12],357⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1480 : RecordDataValid section14Catalog 6 (⟨72,(10),[5,6],[190],1401⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1401,[5,6,8,9,10,12],1406⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1481 : RecordDataValid section14Catalog 6 (⟨72,(11),[1,2,5,6],[150],357⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨357,[1,2,4,5,6,8,9,10,12],358⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1482 : RecordDataValid section14Catalog 6 (⟨72,(11),[5,6],[190],1402⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1402,[5,6,8,9,10,12],1407⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1483 : RecordDataValid section14Catalog 6 (⟨72,(12),[1,2,5,6],[150],354⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨354,[1,2,4,5,6,8,9,10,12],355⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1484 : RecordDataValid section14Catalog 6 (⟨72,(12),[5,6],[190],1399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1399,[5,6,8,9,10,12],1404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1485 : RecordDataValid section14Catalog 6 (⟨72,(13),[1,2,5,6],[150],355⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨355,[1,2,4,5,6,8,9,10,12],356⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1486 : RecordDataValid section14Catalog 6 (⟨72,(13),[5,6],[190],1400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1400,[5,6,8,9,10,12],1405⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1487 : RecordDataValid section14Catalog 6 (⟨72,(14),[1,2,5,6],[150],359⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨359,[1,2,4,5,6,8,9,10,12],360⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1488 : RecordDataValid section14Catalog 6 (⟨72,(14),[5,6],[190],1404⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1404,[5,6,8,9,10,12],1409⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1489 : RecordDataValid section14Catalog 6 (⟨72,(15),[1,2,5,6],[150],357⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨357,[1,2,4,5,6,8,9,10,12],358⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1490 : RecordDataValid section14Catalog 6 (⟨72,(15),[5,6],[190],1402⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1402,[5,6,8,9,10,12],1407⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1491 : RecordDataValid section14Catalog 6 (⟨75,(0),[1,2,5,6],[150],360⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨360,[1,2,3,4,5,6,7,8,9,10,12],361⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1492 : RecordDataValid section14Catalog 6 (⟨75,(0),[1,2,5,6],[190],381⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨381,[1,2,3,4,5,6,7,8,9,10,11,12],382⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1493 : RecordDataValid section14Catalog 6 (⟨75,(1),[1,2,5,6],[150],361⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨361,[1,2,3,4,5,6,7,8,9,10,12],362⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1494 : RecordDataValid section14Catalog 6 (⟨75,(1),[1,2,5,6],[190],382⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨382,[1,2,3,4,5,6,7,8,9,10,11,12],383⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1495 : RecordDataValid section14Catalog 6 (⟨75,(2),[1,2,5,6],[150],362⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨362,[1,2,3,4,5,6,7,8,9,10,12],363⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1496 : RecordDataValid section14Catalog 6 (⟨75,(2),[1,2,5,6],[190],383⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨383,[1,2,3,4,5,6,7,8,9,10,11,12],384⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1497 : RecordDataValid section14Catalog 6 (⟨75,(3),[1,2,5,6],[150],363⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨363,[1,2,3,4,5,6,7,8,9,10,12],364⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1498 : RecordDataValid section14Catalog 6 (⟨75,(3),[1,2,5,6],[190],384⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨384,[1,2,3,4,5,6,7,8,9,10,11,12],385⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1499 : RecordDataValid section14Catalog 6 (⟨77,(0),[1,5,6],[150],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1500 : RecordDataValid section14Catalog 6 (⟨77,(0),[1,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1501 : RecordDataValid section14Catalog 6 (⟨77,(1),[1,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1502 : RecordDataValid section14Catalog 6 (⟨77,(1),[2,5,6],[150],159⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨159,[1,2,3,5,6,7,9,10,11,13,14,15],159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1503 : RecordDataValid section14Catalog 6 (⟨77,(2),[1,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_1472_1504 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1472).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1472).take 32 = [⟨72,(6),[5,6],[190],1403⟩,⟨72,(7),[1,2,5,6],[150],357⟩,⟨72,(7),[5,6],[190],1402⟩,⟨72,(8),[1,2,5,6],[150],354⟩,⟨72,(8),[5,6],[190],1399⟩,⟨72,(9),[1,2,5,6],[150],355⟩,⟨72,(9),[5,6],[190],1400⟩,⟨72,(10),[1,2,5,6],[150],356⟩,⟨72,(10),[5,6],[190],1401⟩,⟨72,(11),[1,2,5,6],[150],357⟩,⟨72,(11),[5,6],[190],1402⟩,⟨72,(12),[1,2,5,6],[150],354⟩,⟨72,(12),[5,6],[190],1399⟩,⟨72,(13),[1,2,5,6],[150],355⟩,⟨72,(13),[5,6],[190],1400⟩,⟨72,(14),[1,2,5,6],[150],359⟩,⟨72,(14),[5,6],[190],1404⟩,⟨72,(15),[1,2,5,6],[150],357⟩,⟨72,(15),[5,6],[190],1402⟩,⟨75,(0),[1,2,5,6],[150],360⟩,⟨75,(0),[1,2,5,6],[190],381⟩,⟨75,(1),[1,2,5,6],[150],361⟩,⟨75,(1),[1,2,5,6],[190],382⟩,⟨75,(2),[1,2,5,6],[150],362⟩,⟨75,(2),[1,2,5,6],[190],383⟩,⟨75,(3),[1,2,5,6],[150],363⟩,⟨75,(3),[1,2,5,6],[190],384⟩,⟨77,(0),[1,5,6],[150],98⟩,⟨77,(0),[1,5,6,13,14],[190],3⟩,⟨77,(1),[1,5,6,13,14],[190],3⟩,⟨77,(1),[2,5,6],[150],159⟩,⟨77,(2),[1,5,6],[150],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1472
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1473
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1474
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1475
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1476
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1477
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1478
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1479
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1480
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1481
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1482
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1483
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1484
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1485
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1486
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1487
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1488
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1489
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1490
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1491
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1492
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1493
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1494
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1495
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1496
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1497
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1498
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1499
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1500
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1501
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1502
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1503
end Section14Records_6_1472_1504

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1472_1504


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1504_1536
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_1504_1536
private theorem valid1504 : RecordDataValid section14Catalog 6 (⟨77,(2),[1,5,6],[190],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1505 : RecordDataValid section14Catalog 6 (⟨77,(3),[1,2,5,6,14],[190],234⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨234,[1,2,5,6,9,10,13,14],234⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1506 : RecordDataValid section14Catalog 6 (⟨77,(3),[1,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1507 : RecordDataValid section14Catalog 6 (⟨77,(4),[1,5,6],[150],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1508 : RecordDataValid section14Catalog 6 (⟨77,(4),[1,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1509 : RecordDataValid section14Catalog 6 (⟨77,(5),[1,2,5,6],[150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1510 : RecordDataValid section14Catalog 6 (⟨77,(5),[1,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1511 : RecordDataValid section14Catalog 6 (⟨77,(6),[1,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1512 : RecordDataValid section14Catalog 6 (⟨77,(6),[1,5,6],[190],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1513 : RecordDataValid section14Catalog 6 (⟨77,(7),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1514 : RecordDataValid section14Catalog 6 (⟨77,(7),[1,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1515 : RecordDataValid section14Catalog 6 (⟨77,(8),[1,2,5,6],[150],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1516 : RecordDataValid section14Catalog 6 (⟨77,(8),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1517 : RecordDataValid section14Catalog 6 (⟨77,(9),[1,2,5,6],[150],159⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨159,[1,2,3,5,6,7,9,10,11,13,14,15],159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1518 : RecordDataValid section14Catalog 6 (⟨77,(9),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1519 : RecordDataValid section14Catalog 6 (⟨77,(10),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1520 : RecordDataValid section14Catalog 6 (⟨77,(10),[1,2,5,6,13,14],[190],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1521 : RecordDataValid section14Catalog 6 (⟨77,(11),[1,2,5,6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1522 : RecordDataValid section14Catalog 6 (⟨77,(11),[1,2,5,6,13,14],[190],234⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨234,[1,2,5,6,9,10,13,14],234⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1523 : RecordDataValid section14Catalog 6 (⟨77,(12),[1,2,5,6],[150],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1524 : RecordDataValid section14Catalog 6 (⟨77,(12),[6,13],[190],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1525 : RecordDataValid section14Catalog 6 (⟨77,(13),[1,2,5,6],[150],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1526 : RecordDataValid section14Catalog 6 (⟨77,(13),[6,13],[190],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1527 : RecordDataValid section14Catalog 6 (⟨77,(14),[1,2,5,6,13],[190],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1528 : RecordDataValid section14Catalog 6 (⟨77,(14),[6],[150],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1529 : RecordDataValid section14Catalog 6 (⟨77,(15),[1,2,5,6,13,14],[190],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1530 : RecordDataValid section14Catalog 6 (⟨77,(15),[6],[150],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1531 : RecordDataValid section14Catalog 6 (⟨79,(0),[1,2,5,6],[150,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1532 : RecordDataValid section14Catalog 6 (⟨79,(1),[1,2,5,6],[150,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1533 : RecordDataValid section14Catalog 6 (⟨79,(2),[1,2,5,6],[150],364⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨364,[1,2,3,4,5,6,7,8,9,10,11,12],365⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1534 : RecordDataValid section14Catalog 6 (⟨79,(2),[5,6],[190],1405⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1405,[5,6,7,8,9,10,12],1410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1535 : RecordDataValid section14Catalog 6 (⟨79,(3),[1,2,5,6],[150,190],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_1504_1536 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1504).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1504).take 32 = [⟨77,(2),[1,5,6],[190],29⟩,⟨77,(3),[1,2,5,6,14],[190],234⟩,⟨77,(3),[1,5,6],[150],3⟩,⟨77,(4),[1,5,6],[150],98⟩,⟨77,(4),[1,5,6,13,14],[190],3⟩,⟨77,(5),[1,2,5,6],[150],2⟩,⟨77,(5),[1,5,6,13,14],[190],3⟩,⟨77,(6),[1,5,6],[150],3⟩,⟨77,(6),[1,5,6],[190],29⟩,⟨77,(7),[1,2,5,6,13,14],[190],2⟩,⟨77,(7),[1,5,6],[150],3⟩,⟨77,(8),[1,2,5,6],[150],98⟩,⟨77,(8),[1,2,5,6,13,14],[190],3⟩,⟨77,(9),[1,2,5,6],[150],159⟩,⟨77,(9),[1,2,5,6,13,14],[190],3⟩,⟨77,(10),[1,2,5,6],[150],3⟩,⟨77,(10),[1,2,5,6,13,14],[190],29⟩,⟨77,(11),[1,2,5,6],[150],3⟩,⟨77,(11),[1,2,5,6,13,14],[190],234⟩,⟨77,(12),[1,2,5,6],[150],99⟩,⟨77,(12),[6,13],[190],99⟩,⟨77,(13),[1,2,5,6],[150],99⟩,⟨77,(13),[6,13],[190],99⟩,⟨77,(14),[1,2,5,6,13],[190],99⟩,⟨77,(14),[6],[150],99⟩,⟨77,(15),[1,2,5,6,13,14],[190],99⟩,⟨77,(15),[6],[150],99⟩,⟨79,(0),[1,2,5,6],[150,190],2⟩,⟨79,(1),[1,2,5,6],[150,190],2⟩,⟨79,(2),[1,2,5,6],[150],364⟩,⟨79,(2),[5,6],[190],1405⟩,⟨79,(3),[1,2,5,6],[150,190],101⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1504
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1505
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1506
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1507
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1508
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1509
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1510
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1511
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1512
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1513
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1514
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1515
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1516
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1517
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1518
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1519
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1520
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1521
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1522
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1523
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1524
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1525
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1526
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1527
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1528
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1529
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1530
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1531
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1532
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1533
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1534
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1535
end Section14Records_6_1504_1536

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_1504_1536

open Freiman
namespace M7Section14Sep18
universe u

theorem all_of_take_drop {α : Type u} (P : α → Prop) (xs : List α) (n : ℕ)
    (ht : ∀ x ∈ xs.take n, P x) (hd : ∀ x ∈ xs.drop n, P x) :
    ∀ x ∈ xs, P x := by
  intro x hx
  have hm : x ∈ xs.take n ++ xs.drop n := by
    simpa only [List.take_append_drop] using hx
  rcases List.mem_append.mp hm with h | h
  · exact ht x h
  · exact hd x h

theorem all_of_chunks {α : Type u} (P : α → Prop) (xs : List α) (lo size : ℕ)
    (ht : ∀ x ∈ (xs.drop lo).take size, P x)
    (hd : ∀ x ∈ xs.drop (lo+size), P x) : ∀ x ∈ xs.drop lo, P x := by
  apply all_of_take_drop P (xs.drop lo) size ht
  simpa only [List.drop_drop] using hd

theorem all_empty {α : Type u} (P : α → Prop) (xs : List α) (h : xs = []) :
    ∀ x ∈ xs, P x := by
  rw [h]
  exact fun x hx => False.elim (List.not_mem_nil hx)
end M7Section14Sep18

namespace M7Section14Sep18
universe u

theorem all_of_interval_split {α : Type u} (P : α → Prop) (xs : List α)
    (lo cut hi : ℕ) (hc : lo ≤ cut) (hh : cut ≤ hi)
    (left : ∀ x ∈ (xs.drop lo).take (cut-lo), P x)
    (right : ∀ x ∈ (xs.drop cut).take (hi-cut), P x) :
    ∀ x ∈ (xs.drop lo).take (hi-lo), P x := by
  have hsum : hi-lo = (cut-lo)+(hi-cut) := by omega
  have hdrop : lo+(cut-lo) = cut := by omega
  rw [hsum, List.take_add, List.drop_drop, hdrop]
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact left x hx
  · exact right x hx
end M7Section14Sep18

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1408).take 128, section14RecordValid section14Catalog 6 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (6 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 6 r
  exact (all_of_interval_split P xs 1408 1472 1536 (by decide) (by decide) (all_of_interval_split P xs 1408 1440 1472 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_1408_1440 hnum) (Freiman.workReverse20260919_s0006_records_1440_1472 hnum)) (all_of_interval_split P xs 1472 1504 1536 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_1472_1504 hnum) (Freiman.workReverse20260919_s0006_records_1504_1536 hnum)))

#print axioms solution
