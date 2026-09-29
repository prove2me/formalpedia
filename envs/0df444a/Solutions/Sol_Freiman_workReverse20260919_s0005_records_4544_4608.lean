-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_4544_4608
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:40:59.645984+00:00
-- url     : https://prove2.me/submissions/159a468c-75a5-4dc3-8fb5-e07dae29e6b3

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4544_4576
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_4544_4576
private theorem valid4544 : RecordDataValid section14Catalog 5 (⟨295,(19),[5],[170],1447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1447,[5,8,9,12],1452⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4545 : RecordDataValid section14Catalog 5 (⟨295,(20),[5],[170],1450⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1450,[5,8,9,12],1455⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4546 : RecordDataValid section14Catalog 5 (⟨295,(21),[5],[170],1450⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1450,[5,8,9,12],1455⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4547 : RecordDataValid section14Catalog 5 (⟨295,(22),[5],[170],1450⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1450,[5,8,9,12],1455⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4548 : RecordDataValid section14Catalog 5 (⟨295,(23),[5],[170],1446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1446,[5,8,9,12],1451⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4549 : RecordDataValid section14Catalog 5 (⟨295,(24),[5],[170],1447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1447,[5,8,9,12],1452⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4550 : RecordDataValid section14Catalog 5 (⟨297,(0),[5],[170],1451⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1451,[5,8,9,12],1456⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4551 : RecordDataValid section14Catalog 5 (⟨297,(1),[5],[170],1452⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1452,[5,8,9,12],1457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4552 : RecordDataValid section14Catalog 5 (⟨297,(2),[5],[170],1453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1453,[5,8,9,12],1458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4553 : RecordDataValid section14Catalog 5 (⟨297,(3),[5],[170],1454⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1454,[5,8,9,12],1459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4554 : RecordDataValid section14Catalog 5 (⟨297,(4),[5],[170],1451⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1451,[5,8,9,12],1456⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4555 : RecordDataValid section14Catalog 5 (⟨297,(5),[5],[170],1452⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1452,[5,8,9,12],1457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4556 : RecordDataValid section14Catalog 5 (⟨297,(6),[5],[170],1455⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1455,[5,8,9,12],1460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4557 : RecordDataValid section14Catalog 5 (⟨297,(7),[5],[170],1454⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1454,[5,8,9,12],1459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4558 : RecordDataValid section14Catalog 5 (⟨297,(8),[5],[170],1451⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1451,[5,8,9,12],1456⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4559 : RecordDataValid section14Catalog 5 (⟨297,(9),[5],[170],1452⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1452,[5,8,9,12],1457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4560 : RecordDataValid section14Catalog 5 (⟨297,(10),[5],[170],1453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1453,[5,8,9,12],1458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4561 : RecordDataValid section14Catalog 5 (⟨297,(11),[5],[170],1454⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1454,[5,8,9,12],1459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4562 : RecordDataValid section14Catalog 5 (⟨297,(12),[5],[170],1451⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1451,[5,8,9,12],1456⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4563 : RecordDataValid section14Catalog 5 (⟨297,(13),[5],[170],1452⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1452,[5,8,9,12],1457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4564 : RecordDataValid section14Catalog 5 (⟨297,(14),[5],[170],1456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1456,[5,8,9,12],1461⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4565 : RecordDataValid section14Catalog 5 (⟨297,(15),[5],[170],1454⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1454,[5,8,9,12],1459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4566 : RecordDataValid section14Catalog 5 (⟨300,(0),[5],[170],1457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1457,[5,8,9,12],1462⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4567 : RecordDataValid section14Catalog 5 (⟨300,(1),[5],[170],1458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1458,[5,8,9,12],1463⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4568 : RecordDataValid section14Catalog 5 (⟨300,(2),[5],[170],1457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1457,[5,8,9,12],1462⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4569 : RecordDataValid section14Catalog 5 (⟨300,(3),[5],[170],1459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1459,[5,8,9,12],1464⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4570 : RecordDataValid section14Catalog 5 (⟨300,(4),[5],[170],1460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1460,[5,8,9,12],1465⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4571 : RecordDataValid section14Catalog 5 (⟨300,(5),[5],[170],1460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1460,[5,8,9,12],1465⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4572 : RecordDataValid section14Catalog 5 (⟨300,(6),[5],[170],1460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1460,[5,8,9,12],1465⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4573 : RecordDataValid section14Catalog 5 (⟨300,(7),[5],[170],1460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1460,[5,8,9,12],1465⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4574 : RecordDataValid section14Catalog 5 (⟨300,(8),[5],[170],1461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1461,[5,8,9,12],1466⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4575 : RecordDataValid section14Catalog 5 (⟨300,(9),[5],[170],1461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1461,[5,8,9,12],1466⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_4544_4576 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4544).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4544).take 32 = [⟨295,(19),[5],[170],1447⟩,⟨295,(20),[5],[170],1450⟩,⟨295,(21),[5],[170],1450⟩,⟨295,(22),[5],[170],1450⟩,⟨295,(23),[5],[170],1446⟩,⟨295,(24),[5],[170],1447⟩,⟨297,(0),[5],[170],1451⟩,⟨297,(1),[5],[170],1452⟩,⟨297,(2),[5],[170],1453⟩,⟨297,(3),[5],[170],1454⟩,⟨297,(4),[5],[170],1451⟩,⟨297,(5),[5],[170],1452⟩,⟨297,(6),[5],[170],1455⟩,⟨297,(7),[5],[170],1454⟩,⟨297,(8),[5],[170],1451⟩,⟨297,(9),[5],[170],1452⟩,⟨297,(10),[5],[170],1453⟩,⟨297,(11),[5],[170],1454⟩,⟨297,(12),[5],[170],1451⟩,⟨297,(13),[5],[170],1452⟩,⟨297,(14),[5],[170],1456⟩,⟨297,(15),[5],[170],1454⟩,⟨300,(0),[5],[170],1457⟩,⟨300,(1),[5],[170],1458⟩,⟨300,(2),[5],[170],1457⟩,⟨300,(3),[5],[170],1459⟩,⟨300,(4),[5],[170],1460⟩,⟨300,(5),[5],[170],1460⟩,⟨300,(6),[5],[170],1460⟩,⟨300,(7),[5],[170],1460⟩,⟨300,(8),[5],[170],1461⟩,⟨300,(9),[5],[170],1461⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4544
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4545
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4546
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4547
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4548
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4549
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4550
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4551
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4552
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4553
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4554
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4555
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4556
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4557
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4558
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4559
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4560
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4561
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4562
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4563
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4564
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4565
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4566
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4567
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4568
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4569
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4570
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4571
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4572
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4573
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4574
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4575
end Section14Records_5_4544_4576

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4544_4576


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4576_4608
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_4576_4608
private theorem valid4576 : RecordDataValid section14Catalog 5 (⟨300,(10),[5],[170],1461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1461,[5,8,9,12],1466⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4577 : RecordDataValid section14Catalog 5 (⟨300,(11),[5],[170],1461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1461,[5,8,9,12],1466⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4578 : RecordDataValid section14Catalog 5 (⟨300,(12),[5],[170],1462⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1462,[5,8,9,12],1467⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4579 : RecordDataValid section14Catalog 5 (⟨300,(13),[5],[170],1462⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1462,[5,8,9,12],1467⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4580 : RecordDataValid section14Catalog 5 (⟨300,(14),[5],[170],1462⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1462,[5,8,9,12],1467⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4581 : RecordDataValid section14Catalog 5 (⟨300,(15),[5],[170],1462⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1462,[5,8,9,12],1467⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4582 : RecordDataValid section14Catalog 5 (⟨302,(0),[5],[170],1463⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1463,[5,8,9,12],1468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4583 : RecordDataValid section14Catalog 5 (⟨302,(1),[5],[170],1464⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1464,[5,8,9,12],1469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4584 : RecordDataValid section14Catalog 5 (⟨302,(2),[5],[170],1465⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1465,[5,8,9,12],1470⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4585 : RecordDataValid section14Catalog 5 (⟨302,(3),[5],[170],1466⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1466,[5,8,9,12],1471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4586 : RecordDataValid section14Catalog 5 (⟨302,(4),[5],[170],1463⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1463,[5,8,9,12],1468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4587 : RecordDataValid section14Catalog 5 (⟨302,(5),[5],[170],1464⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1464,[5,8,9,12],1469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4588 : RecordDataValid section14Catalog 5 (⟨302,(6),[5],[170],1467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1467,[5,8,9,12],1472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4589 : RecordDataValid section14Catalog 5 (⟨302,(7),[5],[170],1466⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1466,[5,8,9,12],1471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4590 : RecordDataValid section14Catalog 5 (⟨302,(8),[5],[170],1463⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1463,[5,8,9,12],1468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4591 : RecordDataValid section14Catalog 5 (⟨302,(9),[5],[170],1464⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1464,[5,8,9,12],1469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4592 : RecordDataValid section14Catalog 5 (⟨302,(10),[5],[170],1465⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1465,[5,8,9,12],1470⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4593 : RecordDataValid section14Catalog 5 (⟨302,(11),[5],[170],1466⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1466,[5,8,9,12],1471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4594 : RecordDataValid section14Catalog 5 (⟨302,(12),[5],[170],1463⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1463,[5,8,9,12],1468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4595 : RecordDataValid section14Catalog 5 (⟨302,(13),[5],[170],1464⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1464,[5,8,9,12],1469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4596 : RecordDataValid section14Catalog 5 (⟨302,(14),[5],[170],1468⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1468,[5,8,9,12],1473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4597 : RecordDataValid section14Catalog 5 (⟨302,(15),[5],[170],1466⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1466,[5,8,9,12],1471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4598 : RecordDataValid section14Catalog 5 (⟨305,(0),[5],[170],1469⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1469,[5,8,9,12],1474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4599 : RecordDataValid section14Catalog 5 (⟨305,(1),[5],[170],1470⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1470,[5,8,9,12],1475⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4600 : RecordDataValid section14Catalog 5 (⟨305,(2),[5],[170],1471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1471,[5,8,9,12],1476⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4601 : RecordDataValid section14Catalog 5 (⟨305,(3),[5],[170],1472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1472,[5,8,9,12],1477⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4602 : RecordDataValid section14Catalog 5 (⟨307,(0),[5],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4603 : RecordDataValid section14Catalog 5 (⟨307,(1),[5],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4604 : RecordDataValid section14Catalog 5 (⟨307,(2),[5],[170],1473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1473,[5,9],1478⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4605 : RecordDataValid section14Catalog 5 (⟨307,(3),[5],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4606 : RecordDataValid section14Catalog 5 (⟨307,(4),[5],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4607 : RecordDataValid section14Catalog 5 (⟨307,(5),[5],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_4576_4608 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4576).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4576).take 32 = [⟨300,(10),[5],[170],1461⟩,⟨300,(11),[5],[170],1461⟩,⟨300,(12),[5],[170],1462⟩,⟨300,(13),[5],[170],1462⟩,⟨300,(14),[5],[170],1462⟩,⟨300,(15),[5],[170],1462⟩,⟨302,(0),[5],[170],1463⟩,⟨302,(1),[5],[170],1464⟩,⟨302,(2),[5],[170],1465⟩,⟨302,(3),[5],[170],1466⟩,⟨302,(4),[5],[170],1463⟩,⟨302,(5),[5],[170],1464⟩,⟨302,(6),[5],[170],1467⟩,⟨302,(7),[5],[170],1466⟩,⟨302,(8),[5],[170],1463⟩,⟨302,(9),[5],[170],1464⟩,⟨302,(10),[5],[170],1465⟩,⟨302,(11),[5],[170],1466⟩,⟨302,(12),[5],[170],1463⟩,⟨302,(13),[5],[170],1464⟩,⟨302,(14),[5],[170],1468⟩,⟨302,(15),[5],[170],1466⟩,⟨305,(0),[5],[170],1469⟩,⟨305,(1),[5],[170],1470⟩,⟨305,(2),[5],[170],1471⟩,⟨305,(3),[5],[170],1472⟩,⟨307,(0),[5],[170],3⟩,⟨307,(1),[5],[170],3⟩,⟨307,(2),[5],[170],1473⟩,⟨307,(3),[5],[170],29⟩,⟨307,(4),[5],[170],3⟩,⟨307,(5),[5],[170],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4576
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4577
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4578
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4579
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4580
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4581
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4582
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4583
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4584
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4585
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4586
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4587
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4588
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4589
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4590
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4591
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4592
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4593
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4594
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4595
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4596
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4597
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4598
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4599
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4600
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4601
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4602
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4603
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4604
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4605
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4606
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4607
end Section14Records_5_4576_4608

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4576_4608

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4544).take 64, section14RecordValid section14Catalog 5 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (5 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 5 r
  exact (all_of_interval_split P xs 4544 4576 4608 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_4544_4576 hnum) (Freiman.workReverse20260919_s0005_records_4576_4608 hnum))

#print axioms solution
