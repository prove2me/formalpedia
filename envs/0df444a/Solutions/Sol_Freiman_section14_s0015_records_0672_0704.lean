-- Prove2me | solution 1 for Freiman.section14_s0015_records_0672_0704
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T19:01:06.238815+00:00
-- url     : https://prove2.me/submissions/510d8e53-66a6-4c96-8ba0-e1f3748907c8

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
namespace Section14Records_15_672_704
private theorem valid672 : RecordDataValid section14Catalog 15 (⟨195,(2),[3,4,8,12,15,16],[10],698⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨698,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],699⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid673 : RecordDataValid section14Catalog 15 (⟨195,(3),[3,4,8,12,15,16],[10],698⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨698,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],699⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid674 : RecordDataValid section14Catalog 15 (⟨195,(4),[3,4,8,12,15,16],[10],699⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨699,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],700⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid675 : RecordDataValid section14Catalog 15 (⟨195,(5),[3,4,8,12,15,16],[10],700⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨700,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],701⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid676 : RecordDataValid section14Catalog 15 (⟨195,(6),[3,4,8,12,15,16],[10],699⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨699,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],700⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid677 : RecordDataValid section14Catalog 15 (⟨195,(7),[3,4,8,12,15,16],[10],701⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨701,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],702⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid678 : RecordDataValid section14Catalog 15 (⟨195,(8),[3,4,7,15,16],[10],702⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨702,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],703⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid679 : RecordDataValid section14Catalog 15 (⟨195,(9),[3,4,7,15,16],[10],703⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨703,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],704⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid680 : RecordDataValid section14Catalog 15 (⟨197,(0),[3,7,15],[10],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid681 : RecordDataValid section14Catalog 15 (⟨197,(1),[3,7,15],[10],454⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨454,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],455⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid682 : RecordDataValid section14Catalog 15 (⟨197,(2),[3,7,15],[10],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid683 : RecordDataValid section14Catalog 15 (⟨197,(3),[3,7,15],[10],455⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨455,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],456⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid684 : RecordDataValid section14Catalog 15 (⟨197,(4),[3,7,15],[10],456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨456,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid685 : RecordDataValid section14Catalog 15 (⟨197,(5),[3,7,15],[10],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid686 : RecordDataValid section14Catalog 15 (⟨197,(6),[3,7,15],[10],454⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨454,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],455⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid687 : RecordDataValid section14Catalog 15 (⟨197,(7),[3,7,15],[10],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid688 : RecordDataValid section14Catalog 15 (⟨197,(8),[3,7,15],[10],455⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨455,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],456⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid689 : RecordDataValid section14Catalog 15 (⟨197,(9),[3,7,15],[10],456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨456,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid690 : RecordDataValid section14Catalog 15 (⟨197,(10),[3,7,15],[10],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid691 : RecordDataValid section14Catalog 15 (⟨197,(11),[3,7,15],[10],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid692 : RecordDataValid section14Catalog 15 (⟨197,(12),[3,7,15],[10],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid693 : RecordDataValid section14Catalog 15 (⟨197,(13),[3,7,15],[10],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid694 : RecordDataValid section14Catalog 15 (⟨197,(14),[3,7,15],[10],456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨456,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid695 : RecordDataValid section14Catalog 15 (⟨197,(15),[3,7,15],[10],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid696 : RecordDataValid section14Catalog 15 (⟨197,(16),[3,7,15],[10],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid697 : RecordDataValid section14Catalog 15 (⟨197,(17),[3,7,15],[10],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid698 : RecordDataValid section14Catalog 15 (⟨197,(18),[3,7,15],[10],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid699 : RecordDataValid section14Catalog 15 (⟨197,(19),[3,7,15],[10],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid700 : RecordDataValid section14Catalog 15 (⟨197,(20),[3,7,15],[10],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid701 : RecordDataValid section14Catalog 15 (⟨197,(21),[3,7,15],[10],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid702 : RecordDataValid section14Catalog 15 (⟨197,(22),[3,7,15],[10],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid703 : RecordDataValid section14Catalog 15 (⟨197,(23),[3,7,15],[10],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 672).take 32, section14RecordValid section14Catalog 15 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 672).take 32 = [⟨195,(2),[3,4,8,12,15,16],[10],698⟩,⟨195,(3),[3,4,8,12,15,16],[10],698⟩,⟨195,(4),[3,4,8,12,15,16],[10],699⟩,⟨195,(5),[3,4,8,12,15,16],[10],700⟩,⟨195,(6),[3,4,8,12,15,16],[10],699⟩,⟨195,(7),[3,4,8,12,15,16],[10],701⟩,⟨195,(8),[3,4,7,15,16],[10],702⟩,⟨195,(9),[3,4,7,15,16],[10],703⟩,⟨197,(0),[3,7,15],[10],453⟩,⟨197,(1),[3,7,15],[10],454⟩,⟨197,(2),[3,7,15],[10],453⟩,⟨197,(3),[3,7,15],[10],455⟩,⟨197,(4),[3,7,15],[10],456⟩,⟨197,(5),[3,7,15],[10],453⟩,⟨197,(6),[3,7,15],[10],454⟩,⟨197,(7),[3,7,15],[10],453⟩,⟨197,(8),[3,7,15],[10],455⟩,⟨197,(9),[3,7,15],[10],456⟩,⟨197,(10),[3,7,15],[10],457⟩,⟨197,(11),[3,7,15],[10],457⟩,⟨197,(12),[3,7,15],[10],457⟩,⟨197,(13),[3,7,15],[10],457⟩,⟨197,(14),[3,7,15],[10],456⟩,⟨197,(15),[3,7,15],[10],458⟩,⟨197,(16),[3,7,15],[10],458⟩,⟨197,(17),[3,7,15],[10],458⟩,⟨197,(18),[3,7,15],[10],458⟩,⟨197,(19),[3,7,15],[10],458⟩,⟨197,(20),[3,7,15],[10],459⟩,⟨197,(21),[3,7,15],[10],459⟩,⟨197,(22),[3,7,15],[10],459⟩,⟨197,(23),[3,7,15],[10],459⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 15 _ hnum valid672
  · exact recordValid_of_data section14Catalog 15 _ hnum valid673
  · exact recordValid_of_data section14Catalog 15 _ hnum valid674
  · exact recordValid_of_data section14Catalog 15 _ hnum valid675
  · exact recordValid_of_data section14Catalog 15 _ hnum valid676
  · exact recordValid_of_data section14Catalog 15 _ hnum valid677
  · exact recordValid_of_data section14Catalog 15 _ hnum valid678
  · exact recordValid_of_data section14Catalog 15 _ hnum valid679
  · exact recordValid_of_data section14Catalog 15 _ hnum valid680
  · exact recordValid_of_data section14Catalog 15 _ hnum valid681
  · exact recordValid_of_data section14Catalog 15 _ hnum valid682
  · exact recordValid_of_data section14Catalog 15 _ hnum valid683
  · exact recordValid_of_data section14Catalog 15 _ hnum valid684
  · exact recordValid_of_data section14Catalog 15 _ hnum valid685
  · exact recordValid_of_data section14Catalog 15 _ hnum valid686
  · exact recordValid_of_data section14Catalog 15 _ hnum valid687
  · exact recordValid_of_data section14Catalog 15 _ hnum valid688
  · exact recordValid_of_data section14Catalog 15 _ hnum valid689
  · exact recordValid_of_data section14Catalog 15 _ hnum valid690
  · exact recordValid_of_data section14Catalog 15 _ hnum valid691
  · exact recordValid_of_data section14Catalog 15 _ hnum valid692
  · exact recordValid_of_data section14Catalog 15 _ hnum valid693
  · exact recordValid_of_data section14Catalog 15 _ hnum valid694
  · exact recordValid_of_data section14Catalog 15 _ hnum valid695
  · exact recordValid_of_data section14Catalog 15 _ hnum valid696
  · exact recordValid_of_data section14Catalog 15 _ hnum valid697
  · exact recordValid_of_data section14Catalog 15 _ hnum valid698
  · exact recordValid_of_data section14Catalog 15 _ hnum valid699
  · exact recordValid_of_data section14Catalog 15 _ hnum valid700
  · exact recordValid_of_data section14Catalog 15 _ hnum valid701
  · exact recordValid_of_data section14Catalog 15 _ hnum valid702
  · exact recordValid_of_data section14Catalog 15 _ hnum valid703
end Section14Records_15_672_704

#print axioms solution
