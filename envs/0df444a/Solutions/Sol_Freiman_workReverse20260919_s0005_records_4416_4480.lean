-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_4416_4480
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:39:50.792998+00:00
-- url     : https://prove2.me/submissions/205dbaa7-4c85-41b9-a3e6-fcae228a940c

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4416_4448
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_4416_4448
private theorem valid4416 : RecordDataValid section14Catalog 5 (⟨283,(1),[5],[170],1121⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1121,[3,5,7,8,9,11,12,15],1125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4417 : RecordDataValid section14Catalog 5 (⟨283,(2),[5],[170],1122⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1122,[3,5,7,8,9,11,12,15],1126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4418 : RecordDataValid section14Catalog 5 (⟨283,(3),[5],[170],1122⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1122,[3,5,7,8,9,11,12,15],1126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4419 : RecordDataValid section14Catalog 5 (⟨283,(4),[5],[170],1123⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1123,[3,5,7,8,9,11,12,15],1127⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4420 : RecordDataValid section14Catalog 5 (⟨283,(5),[5],[170],1120⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1120,[3,5,7,8,9,11,12,15],1124⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4421 : RecordDataValid section14Catalog 5 (⟨283,(6),[5],[170],1121⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1121,[3,5,7,8,9,11,12,15],1125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4422 : RecordDataValid section14Catalog 5 (⟨283,(7),[5],[170],1124⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1124,[3,5,7,8,9,11,12,15],1128⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4423 : RecordDataValid section14Catalog 5 (⟨283,(8),[5],[170],1125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1125,[3,5,7,8,9,11,12,15],1129⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4424 : RecordDataValid section14Catalog 5 (⟨283,(9),[5],[170],1126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1126,[3,5,7,8,9,11,12,15],1130⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4425 : RecordDataValid section14Catalog 5 (⟨285,(0),[5],[170],1430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1430,[5,8,9,12],1435⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4426 : RecordDataValid section14Catalog 5 (⟨285,(1),[5],[170],1430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1430,[5,8,9,12],1435⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4427 : RecordDataValid section14Catalog 5 (⟨285,(2),[5],[170],1431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1431,[5,8,9,12],1436⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4428 : RecordDataValid section14Catalog 5 (⟨285,(3),[5],[170],1432⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1432,[5,8,9,12],1437⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4429 : RecordDataValid section14Catalog 5 (⟨285,(4),[5],[170],1433⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1433,[5,8,9,12],1438⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4430 : RecordDataValid section14Catalog 5 (⟨285,(5),[5],[170],1434⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1434,[5,8,9,12],1439⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4431 : RecordDataValid section14Catalog 5 (⟨285,(6),[5],[170],1434⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1434,[5,8,9,12],1439⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4432 : RecordDataValid section14Catalog 5 (⟨285,(7),[5],[170],1431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1431,[5,8,9,12],1436⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4433 : RecordDataValid section14Catalog 5 (⟨285,(8),[5],[170],1432⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1432,[5,8,9,12],1437⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4434 : RecordDataValid section14Catalog 5 (⟨285,(9),[5],[170],1433⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1433,[5,8,9,12],1438⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4435 : RecordDataValid section14Catalog 5 (⟨285,(10),[5],[170],1430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1430,[5,8,9,12],1435⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4436 : RecordDataValid section14Catalog 5 (⟨285,(11),[5],[170],1430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1430,[5,8,9,12],1435⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4437 : RecordDataValid section14Catalog 5 (⟨285,(12),[5],[170],1431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1431,[5,8,9,12],1436⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4438 : RecordDataValid section14Catalog 5 (⟨285,(13),[5],[170],1432⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1432,[5,8,9,12],1437⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4439 : RecordDataValid section14Catalog 5 (⟨285,(14),[5],[170],1433⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1433,[5,8,9,12],1438⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4440 : RecordDataValid section14Catalog 5 (⟨285,(15),[5],[170],1435⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1435,[5,8,9,12],1440⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4441 : RecordDataValid section14Catalog 5 (⟨285,(16),[5],[170],1435⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1435,[5,8,9,12],1440⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4442 : RecordDataValid section14Catalog 5 (⟨285,(17),[5],[170],1431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1431,[5,8,9,12],1436⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4443 : RecordDataValid section14Catalog 5 (⟨285,(18),[5],[170],1432⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1432,[5,8,9,12],1437⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4444 : RecordDataValid section14Catalog 5 (⟨285,(19),[5],[170],1433⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1433,[5,8,9,12],1438⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4445 : RecordDataValid section14Catalog 5 (⟨285,(20),[5],[170],1436⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1436,[5,8,9,12],1441⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4446 : RecordDataValid section14Catalog 5 (⟨285,(21),[5],[170],1436⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1436,[5,8,9,12],1441⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4447 : RecordDataValid section14Catalog 5 (⟨285,(22),[5],[170],1436⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1436,[5,8,9,12],1441⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_4416_4448 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4416).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4416).take 32 = [⟨283,(1),[5],[170],1121⟩,⟨283,(2),[5],[170],1122⟩,⟨283,(3),[5],[170],1122⟩,⟨283,(4),[5],[170],1123⟩,⟨283,(5),[5],[170],1120⟩,⟨283,(6),[5],[170],1121⟩,⟨283,(7),[5],[170],1124⟩,⟨283,(8),[5],[170],1125⟩,⟨283,(9),[5],[170],1126⟩,⟨285,(0),[5],[170],1430⟩,⟨285,(1),[5],[170],1430⟩,⟨285,(2),[5],[170],1431⟩,⟨285,(3),[5],[170],1432⟩,⟨285,(4),[5],[170],1433⟩,⟨285,(5),[5],[170],1434⟩,⟨285,(6),[5],[170],1434⟩,⟨285,(7),[5],[170],1431⟩,⟨285,(8),[5],[170],1432⟩,⟨285,(9),[5],[170],1433⟩,⟨285,(10),[5],[170],1430⟩,⟨285,(11),[5],[170],1430⟩,⟨285,(12),[5],[170],1431⟩,⟨285,(13),[5],[170],1432⟩,⟨285,(14),[5],[170],1433⟩,⟨285,(15),[5],[170],1435⟩,⟨285,(16),[5],[170],1435⟩,⟨285,(17),[5],[170],1431⟩,⟨285,(18),[5],[170],1432⟩,⟨285,(19),[5],[170],1433⟩,⟨285,(20),[5],[170],1436⟩,⟨285,(21),[5],[170],1436⟩,⟨285,(22),[5],[170],1436⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4416
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4417
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4418
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4419
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4420
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4421
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4422
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4423
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4424
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4425
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4426
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4427
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4428
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4429
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4430
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4431
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4432
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4433
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4434
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4435
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4436
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4437
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4438
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4439
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4440
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4441
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4442
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4443
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4444
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4445
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4446
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4447
end Section14Records_5_4416_4448

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4416_4448


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4448_4480
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_4448_4480
private theorem valid4448 : RecordDataValid section14Catalog 5 (⟨285,(23),[5],[170],1432⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1432,[5,8,9,12],1437⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4449 : RecordDataValid section14Catalog 5 (⟨285,(24),[5],[170],1433⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1433,[5,8,9,12],1438⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4450 : RecordDataValid section14Catalog 5 (⟨288,(0),[5],[170],1134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1134,[3,5,7,8,9,11,12,15],1138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4451 : RecordDataValid section14Catalog 5 (⟨288,(1),[5],[170],1135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1135,[3,5,7,8,9,11,12,15],1139⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4452 : RecordDataValid section14Catalog 5 (⟨288,(2),[5],[170],1136⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1136,[3,5,7,8,9,11,12,15],1140⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4453 : RecordDataValid section14Catalog 5 (⟨288,(3),[5],[170],1136⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1136,[3,5,7,8,9,11,12,15],1140⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4454 : RecordDataValid section14Catalog 5 (⟨288,(4),[5],[170],1136⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1136,[3,5,7,8,9,11,12,15],1140⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4455 : RecordDataValid section14Catalog 5 (⟨288,(5),[5],[170],1134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1134,[3,5,7,8,9,11,12,15],1138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4456 : RecordDataValid section14Catalog 5 (⟨288,(6),[5],[170],1135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1135,[3,5,7,8,9,11,12,15],1139⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4457 : RecordDataValid section14Catalog 5 (⟨288,(7),[5],[170],1137⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1137,[3,5,7,8,9,11,12,15],1141⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4458 : RecordDataValid section14Catalog 5 (⟨288,(8),[5],[170],1138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1138,[3,5,7,8,9,11,12,15],1142⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4459 : RecordDataValid section14Catalog 5 (⟨288,(9),[5],[170],1137⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1137,[3,5,7,8,9,11,12,15],1141⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4460 : RecordDataValid section14Catalog 5 (⟨288,(10),[5],[170],1134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1134,[3,5,7,8,9,11,12,15],1138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4461 : RecordDataValid section14Catalog 5 (⟨288,(11),[5],[170],1135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1135,[3,5,7,8,9,11,12,15],1139⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4462 : RecordDataValid section14Catalog 5 (⟨288,(12),[5],[170],1139⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1139,[3,5,7,8,9,11,12,15],1143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4463 : RecordDataValid section14Catalog 5 (⟨288,(13),[5],[170],1138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1138,[3,5,7,8,9,11,12,15],1142⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4464 : RecordDataValid section14Catalog 5 (⟨288,(14),[5],[170],1139⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1139,[3,5,7,8,9,11,12,15],1143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4465 : RecordDataValid section14Catalog 5 (⟨288,(15),[5],[170],1140⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1140,[3,5,7,8,9,11,12,15],1144⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4466 : RecordDataValid section14Catalog 5 (⟨288,(16),[5],[170],1141⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1141,[3,5,7,8,9,11,12,15],1145⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4467 : RecordDataValid section14Catalog 5 (⟨288,(17),[5],[170],1142⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1142,[3,5,7,8,9,11,12,15],1146⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4468 : RecordDataValid section14Catalog 5 (⟨288,(18),[5],[170],1143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1143,[3,5,7,8,9,11,12,15],1147⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4469 : RecordDataValid section14Catalog 5 (⟨288,(19),[5],[170],1142⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1142,[3,5,7,8,9,11,12,15],1146⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4470 : RecordDataValid section14Catalog 5 (⟨288,(20),[5],[170],1134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1134,[3,5,7,8,9,11,12,15],1138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4471 : RecordDataValid section14Catalog 5 (⟨288,(21),[5],[170],1135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1135,[3,5,7,8,9,11,12,15],1139⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4472 : RecordDataValid section14Catalog 5 (⟨288,(22),[5],[170],1144⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1144,[3,5,7,8,9,11,12,15],1148⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4473 : RecordDataValid section14Catalog 5 (⟨288,(23),[5],[170],1138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1138,[3,5,7,8,9,11,12,15],1142⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4474 : RecordDataValid section14Catalog 5 (⟨288,(24),[5],[170],1144⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1144,[3,5,7,8,9,11,12,15],1148⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4475 : RecordDataValid section14Catalog 5 (⟨290,(0),[5],[170],1437⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1437,[5,8,9,12],1442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4476 : RecordDataValid section14Catalog 5 (⟨290,(1),[5],[170],1437⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1437,[5,8,9,12],1442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4477 : RecordDataValid section14Catalog 5 (⟨290,(2),[5],[170],1438⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1438,[5,8,9,12],1443⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4478 : RecordDataValid section14Catalog 5 (⟨290,(3),[5],[170],1439⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1439,[5,8,9,12],1444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4479 : RecordDataValid section14Catalog 5 (⟨290,(4),[5],[170],1440⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1440,[5,8,9,12],1445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_4448_4480 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4448).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4448).take 32 = [⟨285,(23),[5],[170],1432⟩,⟨285,(24),[5],[170],1433⟩,⟨288,(0),[5],[170],1134⟩,⟨288,(1),[5],[170],1135⟩,⟨288,(2),[5],[170],1136⟩,⟨288,(3),[5],[170],1136⟩,⟨288,(4),[5],[170],1136⟩,⟨288,(5),[5],[170],1134⟩,⟨288,(6),[5],[170],1135⟩,⟨288,(7),[5],[170],1137⟩,⟨288,(8),[5],[170],1138⟩,⟨288,(9),[5],[170],1137⟩,⟨288,(10),[5],[170],1134⟩,⟨288,(11),[5],[170],1135⟩,⟨288,(12),[5],[170],1139⟩,⟨288,(13),[5],[170],1138⟩,⟨288,(14),[5],[170],1139⟩,⟨288,(15),[5],[170],1140⟩,⟨288,(16),[5],[170],1141⟩,⟨288,(17),[5],[170],1142⟩,⟨288,(18),[5],[170],1143⟩,⟨288,(19),[5],[170],1142⟩,⟨288,(20),[5],[170],1134⟩,⟨288,(21),[5],[170],1135⟩,⟨288,(22),[5],[170],1144⟩,⟨288,(23),[5],[170],1138⟩,⟨288,(24),[5],[170],1144⟩,⟨290,(0),[5],[170],1437⟩,⟨290,(1),[5],[170],1437⟩,⟨290,(2),[5],[170],1438⟩,⟨290,(3),[5],[170],1439⟩,⟨290,(4),[5],[170],1440⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4448
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4449
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4450
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4451
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4452
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4453
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4454
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4455
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4456
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4457
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4458
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4459
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4460
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4461
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4462
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4463
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4464
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4465
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4466
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4467
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4468
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4469
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4470
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4471
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4472
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4473
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4474
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4475
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4476
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4477
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4478
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4479
end Section14Records_5_4448_4480

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4448_4480

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4416).take 64, section14RecordValid section14Catalog 5 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (5 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 5 r
  exact (all_of_interval_split P xs 4416 4448 4480 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_4416_4448 hnum) (Freiman.workReverse20260919_s0005_records_4448_4480 hnum))

#print axioms solution
