-- Prove2me | solution 1 for Freiman.section14_s0007_records_0672_0704
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T09:32:53.046854+00:00
-- url     : https://prove2.me/submissions/64c65725-9f90-44b7-9490-d2ed3f77e7a6

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
namespace Section14Records_7_672_704
private theorem valid672 : RecordDataValid section14Catalog 7 (⟨166,(10),[7],[10],1555⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1555,[7],1560⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid673 : RecordDataValid section14Catalog 7 (⟨166,(11),[3,7],[11],648⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨648,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],649⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid674 : RecordDataValid section14Catalog 7 (⟨166,(11),[7],[10],1557⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1557,[7],1562⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid675 : RecordDataValid section14Catalog 7 (⟨166,(12),[3,7],[11],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid676 : RecordDataValid section14Catalog 7 (⟨166,(12),[7],[10],1558⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1558,[7],1563⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid677 : RecordDataValid section14Catalog 7 (⟨166,(13),[3,7],[11],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid678 : RecordDataValid section14Catalog 7 (⟨166,(13),[7],[10],1558⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1558,[7],1563⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid679 : RecordDataValid section14Catalog 7 (⟨166,(14),[3,7],[11],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid680 : RecordDataValid section14Catalog 7 (⟨166,(14),[7],[10],1558⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1558,[7],1563⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid681 : RecordDataValid section14Catalog 7 (⟨166,(15),[3,7],[11],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid682 : RecordDataValid section14Catalog 7 (⟨166,(15),[7],[10],1558⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1558,[7],1563⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid683 : RecordDataValid section14Catalog 7 (⟨167,(0),[3,7],[11],971⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨971,[3,5,6,7],975⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid684 : RecordDataValid section14Catalog 7 (⟨167,(0),[3,7,15],[10],418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨418,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],419⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid685 : RecordDataValid section14Catalog 7 (⟨167,(1),[3,7],[11],972⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨972,[3,5,6,7],976⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid686 : RecordDataValid section14Catalog 7 (⟨167,(1),[3,7,15],[10],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid687 : RecordDataValid section14Catalog 7 (⟨167,(2),[3,7],[11],973⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨973,[3,5,6,7],977⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid688 : RecordDataValid section14Catalog 7 (⟨167,(2),[3,7,15],[10],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid689 : RecordDataValid section14Catalog 7 (⟨167,(3),[3,7],[11],974⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨974,[3,5,6,7],978⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid690 : RecordDataValid section14Catalog 7 (⟨167,(3),[3,7,15],[10],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid691 : RecordDataValid section14Catalog 7 (⟨167,(4),[3,7],[11],975⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨975,[3,5,6,7],979⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid692 : RecordDataValid section14Catalog 7 (⟨167,(4),[3,7,15],[10],422⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨422,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],423⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid693 : RecordDataValid section14Catalog 7 (⟨167,(5),[3,7],[11],972⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨972,[3,5,6,7],976⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid694 : RecordDataValid section14Catalog 7 (⟨167,(5),[3,7,15],[10],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid695 : RecordDataValid section14Catalog 7 (⟨167,(6),[3,7],[11],973⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨973,[3,5,6,7],977⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid696 : RecordDataValid section14Catalog 7 (⟨167,(6),[3,7,15],[10],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid697 : RecordDataValid section14Catalog 7 (⟨167,(7),[3,7],[11],974⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨974,[3,5,6,7],978⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid698 : RecordDataValid section14Catalog 7 (⟨167,(7),[3,7,15],[10],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid699 : RecordDataValid section14Catalog 7 (⟨167,(8),[3,7],[11],971⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨971,[3,5,6,7],975⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid700 : RecordDataValid section14Catalog 7 (⟨167,(8),[3,7,15],[10],418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨418,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],419⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid701 : RecordDataValid section14Catalog 7 (⟨167,(9),[3,7],[11],972⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨972,[3,5,6,7],976⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid702 : RecordDataValid section14Catalog 7 (⟨167,(9),[3,7,15],[10],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid703 : RecordDataValid section14Catalog 7 (⟨167,(10),[3,7],[11],973⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨973,[3,5,6,7],977⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 672).take 32, section14RecordValid section14Catalog 7 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 672).take 32 = [⟨166,(10),[7],[10],1555⟩,⟨166,(11),[3,7],[11],648⟩,⟨166,(11),[7],[10],1557⟩,⟨166,(12),[3,7],[11],649⟩,⟨166,(12),[7],[10],1558⟩,⟨166,(13),[3,7],[11],649⟩,⟨166,(13),[7],[10],1558⟩,⟨166,(14),[3,7],[11],649⟩,⟨166,(14),[7],[10],1558⟩,⟨166,(15),[3,7],[11],649⟩,⟨166,(15),[7],[10],1558⟩,⟨167,(0),[3,7],[11],971⟩,⟨167,(0),[3,7,15],[10],418⟩,⟨167,(1),[3,7],[11],972⟩,⟨167,(1),[3,7,15],[10],419⟩,⟨167,(2),[3,7],[11],973⟩,⟨167,(2),[3,7,15],[10],420⟩,⟨167,(3),[3,7],[11],974⟩,⟨167,(3),[3,7,15],[10],421⟩,⟨167,(4),[3,7],[11],975⟩,⟨167,(4),[3,7,15],[10],422⟩,⟨167,(5),[3,7],[11],972⟩,⟨167,(5),[3,7,15],[10],419⟩,⟨167,(6),[3,7],[11],973⟩,⟨167,(6),[3,7,15],[10],420⟩,⟨167,(7),[3,7],[11],974⟩,⟨167,(7),[3,7,15],[10],421⟩,⟨167,(8),[3,7],[11],971⟩,⟨167,(8),[3,7,15],[10],418⟩,⟨167,(9),[3,7],[11],972⟩,⟨167,(9),[3,7,15],[10],419⟩,⟨167,(10),[3,7],[11],973⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 7 _ hnum valid672
  · exact recordValid_of_data section14Catalog 7 _ hnum valid673
  · exact recordValid_of_data section14Catalog 7 _ hnum valid674
  · exact recordValid_of_data section14Catalog 7 _ hnum valid675
  · exact recordValid_of_data section14Catalog 7 _ hnum valid676
  · exact recordValid_of_data section14Catalog 7 _ hnum valid677
  · exact recordValid_of_data section14Catalog 7 _ hnum valid678
  · exact recordValid_of_data section14Catalog 7 _ hnum valid679
  · exact recordValid_of_data section14Catalog 7 _ hnum valid680
  · exact recordValid_of_data section14Catalog 7 _ hnum valid681
  · exact recordValid_of_data section14Catalog 7 _ hnum valid682
  · exact recordValid_of_data section14Catalog 7 _ hnum valid683
  · exact recordValid_of_data section14Catalog 7 _ hnum valid684
  · exact recordValid_of_data section14Catalog 7 _ hnum valid685
  · exact recordValid_of_data section14Catalog 7 _ hnum valid686
  · exact recordValid_of_data section14Catalog 7 _ hnum valid687
  · exact recordValid_of_data section14Catalog 7 _ hnum valid688
  · exact recordValid_of_data section14Catalog 7 _ hnum valid689
  · exact recordValid_of_data section14Catalog 7 _ hnum valid690
  · exact recordValid_of_data section14Catalog 7 _ hnum valid691
  · exact recordValid_of_data section14Catalog 7 _ hnum valid692
  · exact recordValid_of_data section14Catalog 7 _ hnum valid693
  · exact recordValid_of_data section14Catalog 7 _ hnum valid694
  · exact recordValid_of_data section14Catalog 7 _ hnum valid695
  · exact recordValid_of_data section14Catalog 7 _ hnum valid696
  · exact recordValid_of_data section14Catalog 7 _ hnum valid697
  · exact recordValid_of_data section14Catalog 7 _ hnum valid698
  · exact recordValid_of_data section14Catalog 7 _ hnum valid699
  · exact recordValid_of_data section14Catalog 7 _ hnum valid700
  · exact recordValid_of_data section14Catalog 7 _ hnum valid701
  · exact recordValid_of_data section14Catalog 7 _ hnum valid702
  · exact recordValid_of_data section14Catalog 7 _ hnum valid703
end Section14Records_7_672_704

#print axioms solution
