-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_1760_1792
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:24:24.190471+00:00
-- url     : https://prove2.me/submissions/d45760b0-5953-4f5f-98cd-82510363d059

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
namespace Section14Records_6_1760_1792
private theorem valid1760 : RecordDataValid section14Catalog 6 (⟨106,(8),[1,5,6,13],[170],443⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨443,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1761 : RecordDataValid section14Catalog 6 (⟨106,(9),[1,5,6,13],[170],444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨444,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1762 : RecordDataValid section14Catalog 6 (⟨106,(10),[1,5,6,13],[170],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1763 : RecordDataValid section14Catalog 6 (⟨106,(11),[1,5,6,13],[170],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1764 : RecordDataValid section14Catalog 6 (⟨106,(12),[1,5,6,13],[170],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1765 : RecordDataValid section14Catalog 6 (⟨106,(13),[1,5,6,13],[170],445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1766 : RecordDataValid section14Catalog 6 (⟨106,(14),[1,5,6,13],[170],444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨444,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1767 : RecordDataValid section14Catalog 6 (⟨106,(15),[1,5,6,13],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1768 : RecordDataValid section14Catalog 6 (⟨106,(16),[1,5,6,13],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1769 : RecordDataValid section14Catalog 6 (⟨106,(17),[1,5,6,13],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1770 : RecordDataValid section14Catalog 6 (⟨106,(18),[1,5,6,13],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1771 : RecordDataValid section14Catalog 6 (⟨106,(19),[1,5,6,13],[170],446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1772 : RecordDataValid section14Catalog 6 (⟨106,(20),[1,5,6,13],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1773 : RecordDataValid section14Catalog 6 (⟨106,(21),[1,5,6,13],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1774 : RecordDataValid section14Catalog 6 (⟨106,(22),[1,5,6,13],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1775 : RecordDataValid section14Catalog 6 (⟨106,(23),[1,5,6,13],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1776 : RecordDataValid section14Catalog 6 (⟨106,(24),[1,5,6,13],[170],447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1777 : RecordDataValid section14Catalog 6 (⟨109,(0),[1,5,6,13],[170],448⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨448,[1,4,5,6,8,9,10,12,13,16],449⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1778 : RecordDataValid section14Catalog 6 (⟨109,(1),[1,5,6,13],[170],448⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨448,[1,4,5,6,8,9,10,12,13,16],449⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1779 : RecordDataValid section14Catalog 6 (⟨109,(2),[1,5,6,13],[170],449⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨449,[1,4,5,6,8,9,10,12,13,16],450⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1780 : RecordDataValid section14Catalog 6 (⟨109,(3),[1,5,6,13],[170],449⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨449,[1,4,5,6,8,9,10,12,13,16],450⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1781 : RecordDataValid section14Catalog 6 (⟨109,(4),[1,5,6,13],[170],450⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨450,[1,4,5,6,8,9,10,12,13,16],451⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1782 : RecordDataValid section14Catalog 6 (⟨109,(5),[1,5,6,13],[170],451⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨451,[1,4,5,6,8,9,10,12,13,16],452⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1783 : RecordDataValid section14Catalog 6 (⟨109,(6),[1,5,6,13],[170],450⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨450,[1,4,5,6,8,9,10,12,13,16],451⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1784 : RecordDataValid section14Catalog 6 (⟨109,(7),[1,5,6,13],[170],452⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨452,[1,4,5,6,8,9,10,12,13,16],453⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1785 : RecordDataValid section14Catalog 6 (⟨109,(8),[1,5,6,13],[170],450⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨450,[1,4,5,6,8,9,10,12,13,16],451⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1786 : RecordDataValid section14Catalog 6 (⟨109,(9),[1,5,6,13],[170],451⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨451,[1,4,5,6,8,9,10,12,13,16],452⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1787 : RecordDataValid section14Catalog 6 (⟨111,(0),[1,5,6,13],[170],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1788 : RecordDataValid section14Catalog 6 (⟨111,(1),[1,5,6,13],[170],454⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨454,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],455⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1789 : RecordDataValid section14Catalog 6 (⟨111,(2),[1,5,6,13],[170],453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1790 : RecordDataValid section14Catalog 6 (⟨111,(3),[1,5,6,13],[170],455⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨455,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],456⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1791 : RecordDataValid section14Catalog 6 (⟨111,(4),[1,5,6,13],[170],456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨456,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1760).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1760).take 32 = [⟨106,(8),[1,5,6,13],[170],443⟩,⟨106,(9),[1,5,6,13],[170],444⟩,⟨106,(10),[1,5,6,13],[170],445⟩,⟨106,(11),[1,5,6,13],[170],445⟩,⟨106,(12),[1,5,6,13],[170],445⟩,⟨106,(13),[1,5,6,13],[170],445⟩,⟨106,(14),[1,5,6,13],[170],444⟩,⟨106,(15),[1,5,6,13],[170],446⟩,⟨106,(16),[1,5,6,13],[170],446⟩,⟨106,(17),[1,5,6,13],[170],446⟩,⟨106,(18),[1,5,6,13],[170],446⟩,⟨106,(19),[1,5,6,13],[170],446⟩,⟨106,(20),[1,5,6,13],[170],447⟩,⟨106,(21),[1,5,6,13],[170],447⟩,⟨106,(22),[1,5,6,13],[170],447⟩,⟨106,(23),[1,5,6,13],[170],447⟩,⟨106,(24),[1,5,6,13],[170],447⟩,⟨109,(0),[1,5,6,13],[170],448⟩,⟨109,(1),[1,5,6,13],[170],448⟩,⟨109,(2),[1,5,6,13],[170],449⟩,⟨109,(3),[1,5,6,13],[170],449⟩,⟨109,(4),[1,5,6,13],[170],450⟩,⟨109,(5),[1,5,6,13],[170],451⟩,⟨109,(6),[1,5,6,13],[170],450⟩,⟨109,(7),[1,5,6,13],[170],452⟩,⟨109,(8),[1,5,6,13],[170],450⟩,⟨109,(9),[1,5,6,13],[170],451⟩,⟨111,(0),[1,5,6,13],[170],453⟩,⟨111,(1),[1,5,6,13],[170],454⟩,⟨111,(2),[1,5,6,13],[170],453⟩,⟨111,(3),[1,5,6,13],[170],455⟩,⟨111,(4),[1,5,6,13],[170],456⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1760
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1761
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1762
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1763
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1764
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1765
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1766
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1767
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1768
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1769
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1770
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1771
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1772
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1773
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1774
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1775
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1776
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1777
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1778
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1779
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1780
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1781
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1782
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1783
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1784
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1785
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1786
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1787
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1788
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1789
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1790
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1791
end Section14Records_6_1760_1792

#print axioms solution
