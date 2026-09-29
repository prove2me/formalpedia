-- Prove2me | solution 1 for Freiman.section14_s0014_records_0736_0768
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T01:36:34.137908+00:00
-- url     : https://prove2.me/submissions/ce3fc6c1-99b9-4b1f-91ef-76d3fe4f1863

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
namespace Section14Records_14_736_768
private theorem valid736 : RecordDataValid section14Catalog 14 (⟨45,(15),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid737 : RecordDataValid section14Catalog 14 (⟨45,(16),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid738 : RecordDataValid section14Catalog 14 (⟨45,(17),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid739 : RecordDataValid section14Catalog 14 (⟨45,(18),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid740 : RecordDataValid section14Catalog 14 (⟨45,(19),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid741 : RecordDataValid section14Catalog 14 (⟨45,(20),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid742 : RecordDataValid section14Catalog 14 (⟨45,(21),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid743 : RecordDataValid section14Catalog 14 (⟨45,(22),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid744 : RecordDataValid section14Catalog 14 (⟨45,(23),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid745 : RecordDataValid section14Catalog 14 (⟨45,(24),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid746 : RecordDataValid section14Catalog 14 (⟨47,(0),[1,2,5,6,13,14],[170,174,190],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid747 : RecordDataValid section14Catalog 14 (⟨47,(1),[1,2,5,6,13,14],[170,174,190],260⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨260,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],261⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid748 : RecordDataValid section14Catalog 14 (⟨47,(2),[1,2,5,6,13,14],[170,174,190],261⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨261,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],262⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid749 : RecordDataValid section14Catalog 14 (⟨47,(3),[1,2,5,6,13,14],[170,174,190],262⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨262,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],263⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid750 : RecordDataValid section14Catalog 14 (⟨47,(4),[1,2,5,6,13,14],[170,174,190],263⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨263,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],264⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid751 : RecordDataValid section14Catalog 14 (⟨47,(5),[1,2,5,6,13,14],[170,174,190],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid752 : RecordDataValid section14Catalog 14 (⟨47,(6),[1,2,5,6,13,14],[170,174,190],260⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨260,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],261⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid753 : RecordDataValid section14Catalog 14 (⟨47,(7),[1,2,5,6,13,14],[170],264⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨264,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],265⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid754 : RecordDataValid section14Catalog 14 (⟨47,(7),[1,2,5,6,13,14],[190],319⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨319,[1,2,4,5,6,8,9,10,12,13,14,16],320⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid755 : RecordDataValid section14Catalog 14 (⟨47,(7),[1,2,5,13,14],[174],295⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨295,[1,2,3,5,13,14,15],296⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid756 : RecordDataValid section14Catalog 14 (⟨47,(8),[1,2,5,6,13,14],[170],265⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨265,[1,2,3,4,5,6,7,10,11,13,14,15,16],266⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid757 : RecordDataValid section14Catalog 14 (⟨47,(8),[1,2,5,6,13,14],[190],320⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨320,[1,2,4,5,6,8,9,10,12,13,14,16],321⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid758 : RecordDataValid section14Catalog 14 (⟨47,(8),[1,2,13,14],[174],296⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨296,[1,2,13,14,15],297⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid759 : RecordDataValid section14Catalog 14 (⟨47,(9),[1,2,5,6,13,14],[170],266⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨266,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],267⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid760 : RecordDataValid section14Catalog 14 (⟨47,(9),[1,2,5,6,13,14],[190],321⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨321,[1,2,4,5,6,8,9,10,12,13,14,16],322⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid761 : RecordDataValid section14Catalog 14 (⟨47,(9),[1,2,5,13,14],[174],297⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨297,[1,2,3,5,13,14,15],298⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid762 : RecordDataValid section14Catalog 14 (⟨47,(10),[1,2,5,6,13,14],[170,174,190],194⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨194,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],194⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid763 : RecordDataValid section14Catalog 14 (⟨47,(11),[1,2,5,6,13,14],[170,174,190],267⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨267,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],268⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid764 : RecordDataValid section14Catalog 14 (⟨47,(12),[1,2,5,6,13,14],[170],268⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨268,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],269⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid765 : RecordDataValid section14Catalog 14 (⟨47,(12),[1,2,5,6,13,14],[190],322⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨322,[1,2,4,5,6,8,9,10,12,13,14,16],323⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid766 : RecordDataValid section14Catalog 14 (⟨47,(12),[1,2,5,13,14],[174],298⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨298,[1,2,3,5,6,7,13,14,15],299⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid767 : RecordDataValid section14Catalog 14 (⟨47,(13),[1,2,5,6,13,14],[170],268⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨268,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],269⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 736).take 32, section14RecordValid section14Catalog 14 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 736).take 32 = [⟨45,(15),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(16),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(17),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(18),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(19),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(20),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(21),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(22),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(23),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(24),[1,2,5,6,13,14],[170,174,190],2⟩,⟨47,(0),[1,2,5,6,13,14],[170,174,190],189⟩,⟨47,(1),[1,2,5,6,13,14],[170,174,190],260⟩,⟨47,(2),[1,2,5,6,13,14],[170,174,190],261⟩,⟨47,(3),[1,2,5,6,13,14],[170,174,190],262⟩,⟨47,(4),[1,2,5,6,13,14],[170,174,190],263⟩,⟨47,(5),[1,2,5,6,13,14],[170,174,190],189⟩,⟨47,(6),[1,2,5,6,13,14],[170,174,190],260⟩,⟨47,(7),[1,2,5,6,13,14],[170],264⟩,⟨47,(7),[1,2,5,6,13,14],[190],319⟩,⟨47,(7),[1,2,5,13,14],[174],295⟩,⟨47,(8),[1,2,5,6,13,14],[170],265⟩,⟨47,(8),[1,2,5,6,13,14],[190],320⟩,⟨47,(8),[1,2,13,14],[174],296⟩,⟨47,(9),[1,2,5,6,13,14],[170],266⟩,⟨47,(9),[1,2,5,6,13,14],[190],321⟩,⟨47,(9),[1,2,5,13,14],[174],297⟩,⟨47,(10),[1,2,5,6,13,14],[170,174,190],194⟩,⟨47,(11),[1,2,5,6,13,14],[170,174,190],267⟩,⟨47,(12),[1,2,5,6,13,14],[170],268⟩,⟨47,(12),[1,2,5,6,13,14],[190],322⟩,⟨47,(12),[1,2,5,13,14],[174],298⟩,⟨47,(13),[1,2,5,6,13,14],[170],268⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 14 _ hnum valid736
  · exact recordValid_of_data section14Catalog 14 _ hnum valid737
  · exact recordValid_of_data section14Catalog 14 _ hnum valid738
  · exact recordValid_of_data section14Catalog 14 _ hnum valid739
  · exact recordValid_of_data section14Catalog 14 _ hnum valid740
  · exact recordValid_of_data section14Catalog 14 _ hnum valid741
  · exact recordValid_of_data section14Catalog 14 _ hnum valid742
  · exact recordValid_of_data section14Catalog 14 _ hnum valid743
  · exact recordValid_of_data section14Catalog 14 _ hnum valid744
  · exact recordValid_of_data section14Catalog 14 _ hnum valid745
  · exact recordValid_of_data section14Catalog 14 _ hnum valid746
  · exact recordValid_of_data section14Catalog 14 _ hnum valid747
  · exact recordValid_of_data section14Catalog 14 _ hnum valid748
  · exact recordValid_of_data section14Catalog 14 _ hnum valid749
  · exact recordValid_of_data section14Catalog 14 _ hnum valid750
  · exact recordValid_of_data section14Catalog 14 _ hnum valid751
  · exact recordValid_of_data section14Catalog 14 _ hnum valid752
  · exact recordValid_of_data section14Catalog 14 _ hnum valid753
  · exact recordValid_of_data section14Catalog 14 _ hnum valid754
  · exact recordValid_of_data section14Catalog 14 _ hnum valid755
  · exact recordValid_of_data section14Catalog 14 _ hnum valid756
  · exact recordValid_of_data section14Catalog 14 _ hnum valid757
  · exact recordValid_of_data section14Catalog 14 _ hnum valid758
  · exact recordValid_of_data section14Catalog 14 _ hnum valid759
  · exact recordValid_of_data section14Catalog 14 _ hnum valid760
  · exact recordValid_of_data section14Catalog 14 _ hnum valid761
  · exact recordValid_of_data section14Catalog 14 _ hnum valid762
  · exact recordValid_of_data section14Catalog 14 _ hnum valid763
  · exact recordValid_of_data section14Catalog 14 _ hnum valid764
  · exact recordValid_of_data section14Catalog 14 _ hnum valid765
  · exact recordValid_of_data section14Catalog 14 _ hnum valid766
  · exact recordValid_of_data section14Catalog 14 _ hnum valid767
end Section14Records_14_736_768

#print axioms solution
