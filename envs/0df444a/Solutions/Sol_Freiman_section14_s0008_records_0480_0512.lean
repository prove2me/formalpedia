-- Prove2me | solution 1 for Freiman.section14_s0008_records_0480_0512
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T06:58:25.163817+00:00
-- url     : https://prove2.me/submissions/3a5071e3-ca33-45b4-b2f3-0d8b0ebc3827

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
namespace Section14Records_8_480_512
private theorem valid480 : RecordDataValid section14Catalog 8 (⟨72,(12),[4,8,12],[6],354⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨354,[1,2,4,5,6,8,9,10,12],355⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid481 : RecordDataValid section14Catalog 8 (⟨72,(12),[8,12],[14],1399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1399,[5,6,8,9,10,12],1404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid482 : RecordDataValid section14Catalog 8 (⟨72,(13),[4,8,12],[6],355⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨355,[1,2,4,5,6,8,9,10,12],356⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid483 : RecordDataValid section14Catalog 8 (⟨72,(13),[8,12],[14],1400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1400,[5,6,8,9,10,12],1405⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid484 : RecordDataValid section14Catalog 8 (⟨72,(14),[4,8,12],[6],359⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨359,[1,2,4,5,6,8,9,10,12],360⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid485 : RecordDataValid section14Catalog 8 (⟨72,(14),[8,12],[14],1404⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1404,[5,6,8,9,10,12],1409⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid486 : RecordDataValid section14Catalog 8 (⟨72,(15),[4,8,12],[6],357⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨357,[1,2,4,5,6,8,9,10,12],358⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid487 : RecordDataValid section14Catalog 8 (⟨72,(15),[8,12],[14],1402⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1402,[5,6,8,9,10,12],1407⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid488 : RecordDataValid section14Catalog 8 (⟨75,(0),[4,8,12],[6],360⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨360,[1,2,3,4,5,6,7,8,9,10,12],361⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid489 : RecordDataValid section14Catalog 8 (⟨75,(0),[4,8,12],[14],381⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨381,[1,2,3,4,5,6,7,8,9,10,11,12],382⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid490 : RecordDataValid section14Catalog 8 (⟨75,(1),[4,8,12],[6],361⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨361,[1,2,3,4,5,6,7,8,9,10,12],362⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid491 : RecordDataValid section14Catalog 8 (⟨75,(1),[4,8,12],[14],382⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨382,[1,2,3,4,5,6,7,8,9,10,11,12],383⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid492 : RecordDataValid section14Catalog 8 (⟨75,(2),[4,8,12],[6],362⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨362,[1,2,3,4,5,6,7,8,9,10,12],363⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid493 : RecordDataValid section14Catalog 8 (⟨75,(2),[4,8,12],[14],383⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨383,[1,2,3,4,5,6,7,8,9,10,11,12],384⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid494 : RecordDataValid section14Catalog 8 (⟨75,(3),[4,8,12],[6],363⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨363,[1,2,3,4,5,6,7,8,9,10,12],364⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid495 : RecordDataValid section14Catalog 8 (⟨75,(3),[4,8,12],[14],384⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨384,[1,2,3,4,5,6,7,8,9,10,11,12],385⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid496 : RecordDataValid section14Catalog 8 (⟨79,(0),[4,8,12],[6,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid497 : RecordDataValid section14Catalog 8 (⟨79,(1),[4,8,12],[6,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid498 : RecordDataValid section14Catalog 8 (⟨79,(2),[4,8,12],[6],364⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨364,[1,2,3,4,5,6,7,8,9,10,11,12],365⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid499 : RecordDataValid section14Catalog 8 (⟨79,(2),[8,12],[14],1405⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1405,[5,6,7,8,9,10,12],1410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid500 : RecordDataValid section14Catalog 8 (⟨79,(3),[4,8,12],[6,14],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid501 : RecordDataValid section14Catalog 8 (⟨79,(4),[4,8,12],[6,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid502 : RecordDataValid section14Catalog 8 (⟨79,(5),[4,8,12],[6,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid503 : RecordDataValid section14Catalog 8 (⟨79,(6),[4,8,12],[6],365⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨365,[1,2,4,5,6,8,9,10,12],366⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid504 : RecordDataValid section14Catalog 8 (⟨79,(6),[8,12],[14],1406⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1406,[5,6,8,9,10,12],1411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid505 : RecordDataValid section14Catalog 8 (⟨79,(7),[4,8,12],[6,14],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid506 : RecordDataValid section14Catalog 8 (⟨79,(8),[4,8,12],[6,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid507 : RecordDataValid section14Catalog 8 (⟨79,(9),[4,8,12],[6,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid508 : RecordDataValid section14Catalog 8 (⟨79,(10),[4,8,12],[6,14],339⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨339,[1,2,4,5,6,8,9,10,12],340⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid509 : RecordDataValid section14Catalog 8 (⟨79,(11),[4,8,12],[6,14],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid510 : RecordDataValid section14Catalog 8 (⟨79,(12),[4,8,12],[6,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid511 : RecordDataValid section14Catalog 8 (⟨79,(13),[4,8,12],[6,14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 480).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 480).take 32 = [⟨72,(12),[4,8,12],[6],354⟩,⟨72,(12),[8,12],[14],1399⟩,⟨72,(13),[4,8,12],[6],355⟩,⟨72,(13),[8,12],[14],1400⟩,⟨72,(14),[4,8,12],[6],359⟩,⟨72,(14),[8,12],[14],1404⟩,⟨72,(15),[4,8,12],[6],357⟩,⟨72,(15),[8,12],[14],1402⟩,⟨75,(0),[4,8,12],[6],360⟩,⟨75,(0),[4,8,12],[14],381⟩,⟨75,(1),[4,8,12],[6],361⟩,⟨75,(1),[4,8,12],[14],382⟩,⟨75,(2),[4,8,12],[6],362⟩,⟨75,(2),[4,8,12],[14],383⟩,⟨75,(3),[4,8,12],[6],363⟩,⟨75,(3),[4,8,12],[14],384⟩,⟨79,(0),[4,8,12],[6,14],2⟩,⟨79,(1),[4,8,12],[6,14],2⟩,⟨79,(2),[4,8,12],[6],364⟩,⟨79,(2),[8,12],[14],1405⟩,⟨79,(3),[4,8,12],[6,14],101⟩,⟨79,(4),[4,8,12],[6,14],2⟩,⟨79,(5),[4,8,12],[6,14],2⟩,⟨79,(6),[4,8,12],[6],365⟩,⟨79,(6),[8,12],[14],1406⟩,⟨79,(7),[4,8,12],[6,14],101⟩,⟨79,(8),[4,8,12],[6,14],2⟩,⟨79,(9),[4,8,12],[6,14],2⟩,⟨79,(10),[4,8,12],[6,14],339⟩,⟨79,(11),[4,8,12],[6,14],101⟩,⟨79,(12),[4,8,12],[6,14],2⟩,⟨79,(13),[4,8,12],[6,14],2⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid480
  · exact recordValid_of_data section14Catalog 8 _ hnum valid481
  · exact recordValid_of_data section14Catalog 8 _ hnum valid482
  · exact recordValid_of_data section14Catalog 8 _ hnum valid483
  · exact recordValid_of_data section14Catalog 8 _ hnum valid484
  · exact recordValid_of_data section14Catalog 8 _ hnum valid485
  · exact recordValid_of_data section14Catalog 8 _ hnum valid486
  · exact recordValid_of_data section14Catalog 8 _ hnum valid487
  · exact recordValid_of_data section14Catalog 8 _ hnum valid488
  · exact recordValid_of_data section14Catalog 8 _ hnum valid489
  · exact recordValid_of_data section14Catalog 8 _ hnum valid490
  · exact recordValid_of_data section14Catalog 8 _ hnum valid491
  · exact recordValid_of_data section14Catalog 8 _ hnum valid492
  · exact recordValid_of_data section14Catalog 8 _ hnum valid493
  · exact recordValid_of_data section14Catalog 8 _ hnum valid494
  · exact recordValid_of_data section14Catalog 8 _ hnum valid495
  · exact recordValid_of_data section14Catalog 8 _ hnum valid496
  · exact recordValid_of_data section14Catalog 8 _ hnum valid497
  · exact recordValid_of_data section14Catalog 8 _ hnum valid498
  · exact recordValid_of_data section14Catalog 8 _ hnum valid499
  · exact recordValid_of_data section14Catalog 8 _ hnum valid500
  · exact recordValid_of_data section14Catalog 8 _ hnum valid501
  · exact recordValid_of_data section14Catalog 8 _ hnum valid502
  · exact recordValid_of_data section14Catalog 8 _ hnum valid503
  · exact recordValid_of_data section14Catalog 8 _ hnum valid504
  · exact recordValid_of_data section14Catalog 8 _ hnum valid505
  · exact recordValid_of_data section14Catalog 8 _ hnum valid506
  · exact recordValid_of_data section14Catalog 8 _ hnum valid507
  · exact recordValid_of_data section14Catalog 8 _ hnum valid508
  · exact recordValid_of_data section14Catalog 8 _ hnum valid509
  · exact recordValid_of_data section14Catalog 8 _ hnum valid510
  · exact recordValid_of_data section14Catalog 8 _ hnum valid511
end Section14Records_8_480_512

#print axioms solution
