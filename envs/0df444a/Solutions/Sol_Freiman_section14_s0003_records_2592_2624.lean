-- Prove2me | solution 1 for Freiman.section14_s0003_records_2592_2624
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T13:52:14.933295+00:00
-- url     : https://prove2.me/submissions/eeef1a35-ad73-49cd-ac8e-c50399991936

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
namespace Section14Records_3_2592_2624
private theorem valid2592 : RecordDataValid section14Catalog 3 (⟨470,(13),[3,7,15],[10],1220⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1220,[3,7,11,15],1224⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2593 : RecordDataValid section14Catalog 3 (⟨470,(14),[3,7,15],[10],1221⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1221,[3,7,11,15],1225⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2594 : RecordDataValid section14Catalog 3 (⟨470,(15),[3,7,15],[10],1222⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1222,[3,7,11,15],1226⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2595 : RecordDataValid section14Catalog 3 (⟨471,(0),[3,7,15],[10],1224⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1224,[3,7,11,15],1228⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2596 : RecordDataValid section14Catalog 3 (⟨471,(1),[3,7,15],[10],1224⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1224,[3,7,11,15],1228⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2597 : RecordDataValid section14Catalog 3 (⟨471,(2),[3,7,15],[10],1225⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1225,[3,7,11,15],1229⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2598 : RecordDataValid section14Catalog 3 (⟨471,(3),[3,7,15],[10],1225⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1225,[3,7,11,15],1229⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2599 : RecordDataValid section14Catalog 3 (⟨471,(4),[3,7,15],[10],1226⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1226,[3,7,11,15],1230⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2600 : RecordDataValid section14Catalog 3 (⟨471,(5),[3,7,15],[10],1226⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1226,[3,7,11,15],1230⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2601 : RecordDataValid section14Catalog 3 (⟨471,(6),[3,7,15],[10],1227⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1227,[3,7,11,15],1231⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2602 : RecordDataValid section14Catalog 3 (⟨471,(7),[3,7,15],[10],1227⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1227,[3,7,11,15],1231⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2603 : RecordDataValid section14Catalog 3 (⟨472,(0),[3,7,15],[10],1228⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1228,[3,5,7,8,9,11,12,15],1232⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2604 : RecordDataValid section14Catalog 3 (⟨472,(1),[3,7,15],[10],1229⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1229,[3,5,7,8,9,11,12,15],1233⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2605 : RecordDataValid section14Catalog 3 (⟨472,(2),[3,7,15],[10],1228⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1228,[3,5,7,8,9,11,12,15],1232⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2606 : RecordDataValid section14Catalog 3 (⟨472,(3),[3,7,15],[10],1230⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1230,[3,5,7,8,9,11,12,15],1234⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2607 : RecordDataValid section14Catalog 3 (⟨472,(4),[3,7,15],[10],1231⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1231,[3,5,7,8,9,11,12,15],1235⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2608 : RecordDataValid section14Catalog 3 (⟨472,(5),[3,7,15],[10],1232⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1232,[3,5,7,8,9,11,12,15],1236⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2609 : RecordDataValid section14Catalog 3 (⟨472,(6),[3,7,15],[10],1233⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1233,[3,7,11,15],1237⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2610 : RecordDataValid section14Catalog 3 (⟨472,(7),[3,7,15],[10],1234⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1234,[3,7,11,15],1238⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2611 : RecordDataValid section14Catalog 3 (⟨472,(8),[3,7,15],[10],1235⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1235,[3,5,7,8,9,11,12,15],1239⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2612 : RecordDataValid section14Catalog 3 (⟨472,(9),[3,7,15],[10],1236⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1236,[3,5,7,8,9,11,12,15],1240⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2613 : RecordDataValid section14Catalog 3 (⟨472,(10),[3,7,15],[10],1237⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1237,[3,7,11,15],1241⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2614 : RecordDataValid section14Catalog 3 (⟨472,(11),[3,7,15],[10],1238⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1238,[3,7,11,15],1242⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2615 : RecordDataValid section14Catalog 3 (⟨472,(12),[3,7,15],[10],1239⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1239,[3,5,7,8,9,11,12,15],1243⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2616 : RecordDataValid section14Catalog 3 (⟨472,(13),[3,7,15],[10],1240⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1240,[3,5,7,8,9,11,12,15],1244⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2617 : RecordDataValid section14Catalog 3 (⟨472,(14),[3,7,15],[10],1241⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1241,[3,7,11,15],1245⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2618 : RecordDataValid section14Catalog 3 (⟨472,(15),[3,7,15],[10],1241⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1241,[3,7,11,15],1245⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2619 : RecordDataValid section14Catalog 3 (⟨472,(16),[3,7,15],[10],1242⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1242,[3,5,7,8,9,11,12,15],1246⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2620 : RecordDataValid section14Catalog 3 (⟨472,(17),[3,7,15],[10],1243⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1243,[3,5,7,8,9,11,12,15],1247⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2621 : RecordDataValid section14Catalog 3 (⟨472,(18),[3,7,15],[10],1244⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1244,[3,7,11,15],1248⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2622 : RecordDataValid section14Catalog 3 (⟨472,(19),[3,7,15],[10],1244⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1244,[3,7,11,15],1248⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2623 : RecordDataValid section14Catalog 3 (⟨474,(0),[3,7],[10],1245⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1245,[3,5,7,8,9,11,12],1249⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 2592).take 32, section14RecordValid section14Catalog 3 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 2592).take 32 = [⟨470,(13),[3,7,15],[10],1220⟩,⟨470,(14),[3,7,15],[10],1221⟩,⟨470,(15),[3,7,15],[10],1222⟩,⟨471,(0),[3,7,15],[10],1224⟩,⟨471,(1),[3,7,15],[10],1224⟩,⟨471,(2),[3,7,15],[10],1225⟩,⟨471,(3),[3,7,15],[10],1225⟩,⟨471,(4),[3,7,15],[10],1226⟩,⟨471,(5),[3,7,15],[10],1226⟩,⟨471,(6),[3,7,15],[10],1227⟩,⟨471,(7),[3,7,15],[10],1227⟩,⟨472,(0),[3,7,15],[10],1228⟩,⟨472,(1),[3,7,15],[10],1229⟩,⟨472,(2),[3,7,15],[10],1228⟩,⟨472,(3),[3,7,15],[10],1230⟩,⟨472,(4),[3,7,15],[10],1231⟩,⟨472,(5),[3,7,15],[10],1232⟩,⟨472,(6),[3,7,15],[10],1233⟩,⟨472,(7),[3,7,15],[10],1234⟩,⟨472,(8),[3,7,15],[10],1235⟩,⟨472,(9),[3,7,15],[10],1236⟩,⟨472,(10),[3,7,15],[10],1237⟩,⟨472,(11),[3,7,15],[10],1238⟩,⟨472,(12),[3,7,15],[10],1239⟩,⟨472,(13),[3,7,15],[10],1240⟩,⟨472,(14),[3,7,15],[10],1241⟩,⟨472,(15),[3,7,15],[10],1241⟩,⟨472,(16),[3,7,15],[10],1242⟩,⟨472,(17),[3,7,15],[10],1243⟩,⟨472,(18),[3,7,15],[10],1244⟩,⟨472,(19),[3,7,15],[10],1244⟩,⟨474,(0),[3,7],[10],1245⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2592
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2593
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2594
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2595
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2596
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2597
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2598
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2599
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2600
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2601
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2602
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2603
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2604
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2605
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2606
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2607
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2608
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2609
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2610
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2611
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2612
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2613
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2614
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2615
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2616
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2617
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2618
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2619
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2620
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2621
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2622
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2623
end Section14Records_3_2592_2624

#print axioms solution
