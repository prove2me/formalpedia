-- Prove2me | solution 1 for Freiman.section14_s0012_records_0704_0736
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T04:33:30.470589+00:00
-- url     : https://prove2.me/submissions/a882c982-1d90-44ad-bde4-b9ffef04174f

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
namespace Section14Records_12_704_736
private theorem valid704 : RecordDataValid section14Catalog 12 (⟨121,(8),[4,8,12,16],[10],483⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨483,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],484⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid705 : RecordDataValid section14Catalog 12 (⟨121,(9),[4,8,12,16],[10],484⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨484,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],485⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid706 : RecordDataValid section14Catalog 12 (⟨121,(10),[4,8,12,16],[10],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid707 : RecordDataValid section14Catalog 12 (⟨121,(11),[4,8,12,16],[10],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid708 : RecordDataValid section14Catalog 12 (⟨121,(12),[4,8,12,16],[10],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid709 : RecordDataValid section14Catalog 12 (⟨121,(13),[4,8,12,16],[10],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid710 : RecordDataValid section14Catalog 12 (⟨121,(14),[4,8,12,16],[10],484⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨484,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],485⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid711 : RecordDataValid section14Catalog 12 (⟨121,(15),[4,8,12,16],[10],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid712 : RecordDataValid section14Catalog 12 (⟨121,(16),[4,8,12,16],[10],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid713 : RecordDataValid section14Catalog 12 (⟨121,(17),[4,8,12,16],[10],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid714 : RecordDataValid section14Catalog 12 (⟨121,(18),[4,8,12,16],[10],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid715 : RecordDataValid section14Catalog 12 (⟨121,(19),[4,8,12,16],[10],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid716 : RecordDataValid section14Catalog 12 (⟨121,(20),[4,8,12,16],[10],487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨487,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],488⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid717 : RecordDataValid section14Catalog 12 (⟨121,(21),[4,8,12,16],[10],487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨487,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],488⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid718 : RecordDataValid section14Catalog 12 (⟨121,(22),[4,8,12,16],[10],487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨487,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],488⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid719 : RecordDataValid section14Catalog 12 (⟨121,(23),[4,8,12,16],[10],487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨487,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],488⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid720 : RecordDataValid section14Catalog 12 (⟨121,(24),[4,8,12,16],[10],487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨487,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],488⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid721 : RecordDataValid section14Catalog 12 (⟨124,(0),[4,8,12,16],[10],488⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨488,[1,4,5,6,8,9,10,12,13,16],489⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid722 : RecordDataValid section14Catalog 12 (⟨124,(1),[4,8,12,16],[10],489⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨489,[1,4,5,6,8,9,10,12,13,16],490⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid723 : RecordDataValid section14Catalog 12 (⟨124,(2),[4,8,12,16],[10],490⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨490,[1,4,5,6,8,9,10,12,13,16],491⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid724 : RecordDataValid section14Catalog 12 (⟨124,(3),[4,8,12,16],[10],491⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨491,[1,4,5,6,8,9,10,12,13,16],492⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid725 : RecordDataValid section14Catalog 12 (⟨124,(4),[4,8,12,16],[10],488⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨488,[1,4,5,6,8,9,10,12,13,16],489⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid726 : RecordDataValid section14Catalog 12 (⟨124,(5),[4,8,12,16],[10],489⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨489,[1,4,5,6,8,9,10,12,13,16],490⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid727 : RecordDataValid section14Catalog 12 (⟨124,(6),[4,8,12,16],[10],492⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨492,[1,4,5,6,8,9,10,12,13,16],493⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid728 : RecordDataValid section14Catalog 12 (⟨124,(7),[4,8,12,16],[10],491⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨491,[1,4,5,6,8,9,10,12,13,16],492⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid729 : RecordDataValid section14Catalog 12 (⟨124,(8),[4,8,12,16],[10],488⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨488,[1,4,5,6,8,9,10,12,13,16],489⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid730 : RecordDataValid section14Catalog 12 (⟨124,(9),[4,8,12,16],[10],489⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨489,[1,4,5,6,8,9,10,12,13,16],490⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid731 : RecordDataValid section14Catalog 12 (⟨124,(10),[4,8,12,16],[10],490⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨490,[1,4,5,6,8,9,10,12,13,16],491⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid732 : RecordDataValid section14Catalog 12 (⟨124,(11),[4,8,12,16],[10],491⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨491,[1,4,5,6,8,9,10,12,13,16],492⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid733 : RecordDataValid section14Catalog 12 (⟨124,(12),[4,8,12,16],[10],488⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨488,[1,4,5,6,8,9,10,12,13,16],489⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid734 : RecordDataValid section14Catalog 12 (⟨124,(13),[4,8,12,16],[10],489⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨489,[1,4,5,6,8,9,10,12,13,16],490⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid735 : RecordDataValid section14Catalog 12 (⟨124,(14),[4,8,12,16],[10],493⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨493,[1,4,5,6,8,9,10,12,13,16],494⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 704).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 704).take 32 = [⟨121,(8),[4,8,12,16],[10],483⟩,⟨121,(9),[4,8,12,16],[10],484⟩,⟨121,(10),[4,8,12,16],[10],485⟩,⟨121,(11),[4,8,12,16],[10],485⟩,⟨121,(12),[4,8,12,16],[10],485⟩,⟨121,(13),[4,8,12,16],[10],485⟩,⟨121,(14),[4,8,12,16],[10],484⟩,⟨121,(15),[4,8,12,16],[10],486⟩,⟨121,(16),[4,8,12,16],[10],486⟩,⟨121,(17),[4,8,12,16],[10],486⟩,⟨121,(18),[4,8,12,16],[10],486⟩,⟨121,(19),[4,8,12,16],[10],486⟩,⟨121,(20),[4,8,12,16],[10],487⟩,⟨121,(21),[4,8,12,16],[10],487⟩,⟨121,(22),[4,8,12,16],[10],487⟩,⟨121,(23),[4,8,12,16],[10],487⟩,⟨121,(24),[4,8,12,16],[10],487⟩,⟨124,(0),[4,8,12,16],[10],488⟩,⟨124,(1),[4,8,12,16],[10],489⟩,⟨124,(2),[4,8,12,16],[10],490⟩,⟨124,(3),[4,8,12,16],[10],491⟩,⟨124,(4),[4,8,12,16],[10],488⟩,⟨124,(5),[4,8,12,16],[10],489⟩,⟨124,(6),[4,8,12,16],[10],492⟩,⟨124,(7),[4,8,12,16],[10],491⟩,⟨124,(8),[4,8,12,16],[10],488⟩,⟨124,(9),[4,8,12,16],[10],489⟩,⟨124,(10),[4,8,12,16],[10],490⟩,⟨124,(11),[4,8,12,16],[10],491⟩,⟨124,(12),[4,8,12,16],[10],488⟩,⟨124,(13),[4,8,12,16],[10],489⟩,⟨124,(14),[4,8,12,16],[10],493⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid704
  · exact recordValid_of_data section14Catalog 12 _ hnum valid705
  · exact recordValid_of_data section14Catalog 12 _ hnum valid706
  · exact recordValid_of_data section14Catalog 12 _ hnum valid707
  · exact recordValid_of_data section14Catalog 12 _ hnum valid708
  · exact recordValid_of_data section14Catalog 12 _ hnum valid709
  · exact recordValid_of_data section14Catalog 12 _ hnum valid710
  · exact recordValid_of_data section14Catalog 12 _ hnum valid711
  · exact recordValid_of_data section14Catalog 12 _ hnum valid712
  · exact recordValid_of_data section14Catalog 12 _ hnum valid713
  · exact recordValid_of_data section14Catalog 12 _ hnum valid714
  · exact recordValid_of_data section14Catalog 12 _ hnum valid715
  · exact recordValid_of_data section14Catalog 12 _ hnum valid716
  · exact recordValid_of_data section14Catalog 12 _ hnum valid717
  · exact recordValid_of_data section14Catalog 12 _ hnum valid718
  · exact recordValid_of_data section14Catalog 12 _ hnum valid719
  · exact recordValid_of_data section14Catalog 12 _ hnum valid720
  · exact recordValid_of_data section14Catalog 12 _ hnum valid721
  · exact recordValid_of_data section14Catalog 12 _ hnum valid722
  · exact recordValid_of_data section14Catalog 12 _ hnum valid723
  · exact recordValid_of_data section14Catalog 12 _ hnum valid724
  · exact recordValid_of_data section14Catalog 12 _ hnum valid725
  · exact recordValid_of_data section14Catalog 12 _ hnum valid726
  · exact recordValid_of_data section14Catalog 12 _ hnum valid727
  · exact recordValid_of_data section14Catalog 12 _ hnum valid728
  · exact recordValid_of_data section14Catalog 12 _ hnum valid729
  · exact recordValid_of_data section14Catalog 12 _ hnum valid730
  · exact recordValid_of_data section14Catalog 12 _ hnum valid731
  · exact recordValid_of_data section14Catalog 12 _ hnum valid732
  · exact recordValid_of_data section14Catalog 12 _ hnum valid733
  · exact recordValid_of_data section14Catalog 12 _ hnum valid734
  · exact recordValid_of_data section14Catalog 12 _ hnum valid735
end Section14Records_12_704_736

#print axioms solution
