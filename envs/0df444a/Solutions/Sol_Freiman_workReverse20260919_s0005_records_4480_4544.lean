-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_4480_4544
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:52:33.541782+00:00
-- url     : https://prove2.me/submissions/9191b7ad-ce77-40c6-8aa2-14f56df2a304

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4480_4512
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_4480_4512
private theorem valid4480 : RecordDataValid section14Catalog 5 (⟨290,(5),[5],[170],1441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1441,[5,8,9,12],1446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4481 : RecordDataValid section14Catalog 5 (⟨290,(6),[5],[170],1441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1441,[5,8,9,12],1446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4482 : RecordDataValid section14Catalog 5 (⟨290,(7),[5],[170],1438⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1438,[5,8,9,12],1443⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4483 : RecordDataValid section14Catalog 5 (⟨290,(8),[5],[170],1439⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1439,[5,8,9,12],1444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4484 : RecordDataValid section14Catalog 5 (⟨290,(9),[5],[170],1440⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1440,[5,8,9,12],1445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4485 : RecordDataValid section14Catalog 5 (⟨290,(10),[5],[170],1437⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1437,[5,8,9,12],1442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4486 : RecordDataValid section14Catalog 5 (⟨290,(11),[5],[170],1437⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1437,[5,8,9,12],1442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4487 : RecordDataValid section14Catalog 5 (⟨290,(12),[5],[170],1438⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1438,[5,8,9,12],1443⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4488 : RecordDataValid section14Catalog 5 (⟨290,(13),[5],[170],1439⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1439,[5,8,9,12],1444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4489 : RecordDataValid section14Catalog 5 (⟨290,(14),[5],[170],1440⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1440,[5,8,9,12],1445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4490 : RecordDataValid section14Catalog 5 (⟨290,(15),[5],[170],1442⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1442,[5,8,9,12],1447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4491 : RecordDataValid section14Catalog 5 (⟨290,(16),[5],[170],1442⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1442,[5,8,9,12],1447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4492 : RecordDataValid section14Catalog 5 (⟨290,(17),[5],[170],1438⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1438,[5,8,9,12],1443⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4493 : RecordDataValid section14Catalog 5 (⟨290,(18),[5],[170],1439⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1439,[5,8,9,12],1444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4494 : RecordDataValid section14Catalog 5 (⟨290,(19),[5],[170],1440⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1440,[5,8,9,12],1445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4495 : RecordDataValid section14Catalog 5 (⟨290,(20),[5],[170],1443⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1443,[5,8,9,12],1448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4496 : RecordDataValid section14Catalog 5 (⟨290,(21),[5],[170],1443⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1443,[5,8,9,12],1448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4497 : RecordDataValid section14Catalog 5 (⟨290,(22),[5],[170],1443⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1443,[5,8,9,12],1448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4498 : RecordDataValid section14Catalog 5 (⟨290,(23),[5],[170],1439⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1439,[5,8,9,12],1444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4499 : RecordDataValid section14Catalog 5 (⟨290,(24),[5],[170],1440⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1440,[5,8,9,12],1445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4500 : RecordDataValid section14Catalog 5 (⟨293,(0),[5],[170],1152⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1152,[3,5,7,8,9,11,12,15],1156⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4501 : RecordDataValid section14Catalog 5 (⟨293,(1),[5],[170],1153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1153,[3,5,7,8,9,11,12,15],1157⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4502 : RecordDataValid section14Catalog 5 (⟨293,(2),[5],[170],1154⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1154,[3,5,7,8,9,11,12,15],1158⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4503 : RecordDataValid section14Catalog 5 (⟨293,(3),[5],[170],1154⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1154,[3,5,7,8,9,11,12,15],1158⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4504 : RecordDataValid section14Catalog 5 (⟨293,(4),[5],[170],1154⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1154,[3,5,7,8,9,11,12,15],1158⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4505 : RecordDataValid section14Catalog 5 (⟨293,(5),[5],[170],1152⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1152,[3,5,7,8,9,11,12,15],1156⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4506 : RecordDataValid section14Catalog 5 (⟨293,(6),[5],[170],1153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1153,[3,5,7,8,9,11,12,15],1157⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4507 : RecordDataValid section14Catalog 5 (⟨293,(7),[5],[170],1155⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1155,[3,5,7,8,9,11,12,15],1159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4508 : RecordDataValid section14Catalog 5 (⟨293,(8),[5],[170],1156⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1156,[3,5,7,8,9,11,12,15],1160⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4509 : RecordDataValid section14Catalog 5 (⟨293,(9),[5],[170],1155⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1155,[3,5,7,8,9,11,12,15],1159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4510 : RecordDataValid section14Catalog 5 (⟨293,(10),[5],[170],1152⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1152,[3,5,7,8,9,11,12,15],1156⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4511 : RecordDataValid section14Catalog 5 (⟨293,(11),[5],[170],1153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1153,[3,5,7,8,9,11,12,15],1157⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_4480_4512 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4480).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4480).take 32 = [⟨290,(5),[5],[170],1441⟩,⟨290,(6),[5],[170],1441⟩,⟨290,(7),[5],[170],1438⟩,⟨290,(8),[5],[170],1439⟩,⟨290,(9),[5],[170],1440⟩,⟨290,(10),[5],[170],1437⟩,⟨290,(11),[5],[170],1437⟩,⟨290,(12),[5],[170],1438⟩,⟨290,(13),[5],[170],1439⟩,⟨290,(14),[5],[170],1440⟩,⟨290,(15),[5],[170],1442⟩,⟨290,(16),[5],[170],1442⟩,⟨290,(17),[5],[170],1438⟩,⟨290,(18),[5],[170],1439⟩,⟨290,(19),[5],[170],1440⟩,⟨290,(20),[5],[170],1443⟩,⟨290,(21),[5],[170],1443⟩,⟨290,(22),[5],[170],1443⟩,⟨290,(23),[5],[170],1439⟩,⟨290,(24),[5],[170],1440⟩,⟨293,(0),[5],[170],1152⟩,⟨293,(1),[5],[170],1153⟩,⟨293,(2),[5],[170],1154⟩,⟨293,(3),[5],[170],1154⟩,⟨293,(4),[5],[170],1154⟩,⟨293,(5),[5],[170],1152⟩,⟨293,(6),[5],[170],1153⟩,⟨293,(7),[5],[170],1155⟩,⟨293,(8),[5],[170],1156⟩,⟨293,(9),[5],[170],1155⟩,⟨293,(10),[5],[170],1152⟩,⟨293,(11),[5],[170],1153⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4480
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4481
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4482
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4483
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4484
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4485
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4486
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4487
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4488
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4489
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4490
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4491
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4492
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4493
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4494
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4495
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4496
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4497
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4498
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4499
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4500
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4501
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4502
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4503
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4504
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4505
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4506
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4507
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4508
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4509
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4510
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4511
end Section14Records_5_4480_4512

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4480_4512


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4512_4544
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_4512_4544
private theorem valid4512 : RecordDataValid section14Catalog 5 (⟨293,(12),[5],[170],1157⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1157,[3,5,7,8,9,11,12,15],1161⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4513 : RecordDataValid section14Catalog 5 (⟨293,(13),[5],[170],1156⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1156,[3,5,7,8,9,11,12,15],1160⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4514 : RecordDataValid section14Catalog 5 (⟨293,(14),[5],[170],1157⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1157,[3,5,7,8,9,11,12,15],1161⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4515 : RecordDataValid section14Catalog 5 (⟨293,(15),[5],[170],1152⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1152,[3,5,7,8,9,11,12,15],1156⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4516 : RecordDataValid section14Catalog 5 (⟨293,(16),[5],[170],1153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1153,[3,5,7,8,9,11,12,15],1157⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4517 : RecordDataValid section14Catalog 5 (⟨293,(17),[5],[170],1155⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1155,[3,5,7,8,9,11,12,15],1159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4518 : RecordDataValid section14Catalog 5 (⟨293,(18),[5],[170],1156⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1156,[3,5,7,8,9,11,12,15],1160⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4519 : RecordDataValid section14Catalog 5 (⟨293,(19),[5],[170],1155⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1155,[3,5,7,8,9,11,12,15],1159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4520 : RecordDataValid section14Catalog 5 (⟨293,(20),[5],[170],1152⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1152,[3,5,7,8,9,11,12,15],1156⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4521 : RecordDataValid section14Catalog 5 (⟨293,(21),[5],[170],1153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1153,[3,5,7,8,9,11,12,15],1157⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4522 : RecordDataValid section14Catalog 5 (⟨293,(22),[5],[170],1158⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1158,[3,5,7,8,9,11,12,15],1162⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4523 : RecordDataValid section14Catalog 5 (⟨293,(23),[5],[170],1156⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1156,[3,5,7,8,9,11,12,15],1160⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4524 : RecordDataValid section14Catalog 5 (⟨293,(24),[5],[170],1158⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1158,[3,5,7,8,9,11,12,15],1162⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4525 : RecordDataValid section14Catalog 5 (⟨295,(0),[5],[170],1444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1444,[5,8,9,12],1449⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4526 : RecordDataValid section14Catalog 5 (⟨295,(1),[5],[170],1444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1444,[5,8,9,12],1449⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4527 : RecordDataValid section14Catalog 5 (⟨295,(2),[5],[170],1445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1445,[5,8,9,12],1450⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4528 : RecordDataValid section14Catalog 5 (⟨295,(3),[5],[170],1446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1446,[5,8,9,12],1451⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4529 : RecordDataValid section14Catalog 5 (⟨295,(4),[5],[170],1447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1447,[5,8,9,12],1452⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4530 : RecordDataValid section14Catalog 5 (⟨295,(5),[5],[170],1448⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1448,[5,8,9,12],1453⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4531 : RecordDataValid section14Catalog 5 (⟨295,(6),[5],[170],1448⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1448,[5,8,9,12],1453⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4532 : RecordDataValid section14Catalog 5 (⟨295,(7),[5],[170],1445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1445,[5,8,9,12],1450⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4533 : RecordDataValid section14Catalog 5 (⟨295,(8),[5],[170],1446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1446,[5,8,9,12],1451⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4534 : RecordDataValid section14Catalog 5 (⟨295,(9),[5],[170],1447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1447,[5,8,9,12],1452⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4535 : RecordDataValid section14Catalog 5 (⟨295,(10),[5],[170],1444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1444,[5,8,9,12],1449⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4536 : RecordDataValid section14Catalog 5 (⟨295,(11),[5],[170],1444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1444,[5,8,9,12],1449⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4537 : RecordDataValid section14Catalog 5 (⟨295,(12),[5],[170],1445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1445,[5,8,9,12],1450⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4538 : RecordDataValid section14Catalog 5 (⟨295,(13),[5],[170],1446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1446,[5,8,9,12],1451⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4539 : RecordDataValid section14Catalog 5 (⟨295,(14),[5],[170],1447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1447,[5,8,9,12],1452⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4540 : RecordDataValid section14Catalog 5 (⟨295,(15),[5],[170],1449⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1449,[5,8,9,12],1454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4541 : RecordDataValid section14Catalog 5 (⟨295,(16),[5],[170],1449⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1449,[5,8,9,12],1454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4542 : RecordDataValid section14Catalog 5 (⟨295,(17),[5],[170],1445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1445,[5,8,9,12],1450⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4543 : RecordDataValid section14Catalog 5 (⟨295,(18),[5],[170],1446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1446,[5,8,9,12],1451⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_4512_4544 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4512).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4512).take 32 = [⟨293,(12),[5],[170],1157⟩,⟨293,(13),[5],[170],1156⟩,⟨293,(14),[5],[170],1157⟩,⟨293,(15),[5],[170],1152⟩,⟨293,(16),[5],[170],1153⟩,⟨293,(17),[5],[170],1155⟩,⟨293,(18),[5],[170],1156⟩,⟨293,(19),[5],[170],1155⟩,⟨293,(20),[5],[170],1152⟩,⟨293,(21),[5],[170],1153⟩,⟨293,(22),[5],[170],1158⟩,⟨293,(23),[5],[170],1156⟩,⟨293,(24),[5],[170],1158⟩,⟨295,(0),[5],[170],1444⟩,⟨295,(1),[5],[170],1444⟩,⟨295,(2),[5],[170],1445⟩,⟨295,(3),[5],[170],1446⟩,⟨295,(4),[5],[170],1447⟩,⟨295,(5),[5],[170],1448⟩,⟨295,(6),[5],[170],1448⟩,⟨295,(7),[5],[170],1445⟩,⟨295,(8),[5],[170],1446⟩,⟨295,(9),[5],[170],1447⟩,⟨295,(10),[5],[170],1444⟩,⟨295,(11),[5],[170],1444⟩,⟨295,(12),[5],[170],1445⟩,⟨295,(13),[5],[170],1446⟩,⟨295,(14),[5],[170],1447⟩,⟨295,(15),[5],[170],1449⟩,⟨295,(16),[5],[170],1449⟩,⟨295,(17),[5],[170],1445⟩,⟨295,(18),[5],[170],1446⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4512
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4513
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4514
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4515
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4516
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4517
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4518
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4519
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4520
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4521
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4522
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4523
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4524
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4525
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4526
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4527
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4528
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4529
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4530
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4531
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4532
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4533
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4534
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4535
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4536
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4537
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4538
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4539
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4540
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4541
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4542
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4543
end Section14Records_5_4512_4544

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4512_4544

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4480).take 64, section14RecordValid section14Catalog 5 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (5 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 5 r
  exact (all_of_interval_split P xs 4480 4512 4544 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_4480_4512 hnum) (Freiman.workReverse20260919_s0005_records_4512_4544 hnum))

#print axioms solution
