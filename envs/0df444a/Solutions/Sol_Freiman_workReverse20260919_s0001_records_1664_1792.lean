-- Prove2me | solution 1 for Freiman.workReverse20260919_s0001_records_1664_1792
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T01:20:02.731001+00:00
-- url     : https://prove2.me/submissions/4b609681-a1d2-403f-ad69-6b241c6b1c59

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1664_1696
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_1664_1696
private theorem valid1664 : RecordDataValid section14Catalog 1 (⟨42,(22),[1,2,5,6,13,14],[170],259⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨259,[1,2,3,4,5,6,7,8,13,14,15,16],260⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1665 : RecordDataValid section14Catalog 1 (⟨42,(22),[1,2,5,6,13,14],[174],294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨294,[1,2,3,5,6,7,13,14,15],295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1666 : RecordDataValid section14Catalog 1 (⟨42,(22),[1,2,5,6,13,14],[190],318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨318,[1,2,4,5,6,8,13,14,16],319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1667 : RecordDataValid section14Catalog 1 (⟨42,(22),[1,5,13],[186],318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨318,[1,2,4,5,6,8,13,14,16],319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1668 : RecordDataValid section14Catalog 1 (⟨42,(23),[1,2,5,6,13,14],[170],259⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨259,[1,2,3,4,5,6,7,8,13,14,15,16],260⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1669 : RecordDataValid section14Catalog 1 (⟨42,(23),[1,2,5,6,13,14],[174],294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨294,[1,2,3,5,6,7,13,14,15],295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1670 : RecordDataValid section14Catalog 1 (⟨42,(23),[1,2,5,6,13,14],[190],318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨318,[1,2,4,5,6,8,13,14,16],319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1671 : RecordDataValid section14Catalog 1 (⟨42,(23),[1,5,13],[186],318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨318,[1,2,4,5,6,8,13,14,16],319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1672 : RecordDataValid section14Catalog 1 (⟨42,(24),[1,2,5,6,13,14],[170],259⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨259,[1,2,3,4,5,6,7,8,13,14,15,16],260⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1673 : RecordDataValid section14Catalog 1 (⟨42,(24),[1,2,5,6,13,14],[174],294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨294,[1,2,3,5,6,7,13,14,15],295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1674 : RecordDataValid section14Catalog 1 (⟨42,(24),[1,2,5,6,13,14],[190],318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨318,[1,2,4,5,6,8,13,14,16],319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1675 : RecordDataValid section14Catalog 1 (⟨42,(24),[1,5,13],[186],318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨318,[1,2,4,5,6,8,13,14,16],319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1676 : RecordDataValid section14Catalog 1 (⟨45,(0),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1677 : RecordDataValid section14Catalog 1 (⟨45,(0),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1678 : RecordDataValid section14Catalog 1 (⟨45,(1),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1679 : RecordDataValid section14Catalog 1 (⟨45,(1),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1680 : RecordDataValid section14Catalog 1 (⟨45,(2),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1681 : RecordDataValid section14Catalog 1 (⟨45,(2),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1682 : RecordDataValid section14Catalog 1 (⟨45,(3),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1683 : RecordDataValid section14Catalog 1 (⟨45,(3),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1684 : RecordDataValid section14Catalog 1 (⟨45,(4),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1685 : RecordDataValid section14Catalog 1 (⟨45,(4),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1686 : RecordDataValid section14Catalog 1 (⟨45,(5),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1687 : RecordDataValid section14Catalog 1 (⟨45,(5),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1688 : RecordDataValid section14Catalog 1 (⟨45,(6),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1689 : RecordDataValid section14Catalog 1 (⟨45,(6),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1690 : RecordDataValid section14Catalog 1 (⟨45,(7),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1691 : RecordDataValid section14Catalog 1 (⟨45,(7),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1692 : RecordDataValid section14Catalog 1 (⟨45,(8),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1693 : RecordDataValid section14Catalog 1 (⟨45,(8),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1694 : RecordDataValid section14Catalog 1 (⟨45,(9),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1695 : RecordDataValid section14Catalog 1 (⟨45,(9),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_1664_1696 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1664).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1664).take 32 = [⟨42,(22),[1,2,5,6,13,14],[170],259⟩,⟨42,(22),[1,2,5,6,13,14],[174],294⟩,⟨42,(22),[1,2,5,6,13,14],[190],318⟩,⟨42,(22),[1,5,13],[186],318⟩,⟨42,(23),[1,2,5,6,13,14],[170],259⟩,⟨42,(23),[1,2,5,6,13,14],[174],294⟩,⟨42,(23),[1,2,5,6,13,14],[190],318⟩,⟨42,(23),[1,5,13],[186],318⟩,⟨42,(24),[1,2,5,6,13,14],[170],259⟩,⟨42,(24),[1,2,5,6,13,14],[174],294⟩,⟨42,(24),[1,2,5,6,13,14],[190],318⟩,⟨42,(24),[1,5,13],[186],318⟩,⟨45,(0),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(0),[1,5,13],[186],2⟩,⟨45,(1),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(1),[1,5,13],[186],2⟩,⟨45,(2),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(2),[1,5,13],[186],2⟩,⟨45,(3),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(3),[1,5,13],[186],2⟩,⟨45,(4),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(4),[1,5,13],[186],2⟩,⟨45,(5),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(5),[1,5,13],[186],2⟩,⟨45,(6),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(6),[1,5,13],[186],2⟩,⟨45,(7),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(7),[1,5,13],[186],2⟩,⟨45,(8),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(8),[1,5,13],[186],2⟩,⟨45,(9),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(9),[1,5,13],[186],2⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1664
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1665
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1666
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1667
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1668
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1669
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1670
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1671
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1672
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1673
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1674
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1675
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1676
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1677
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1678
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1679
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1680
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1681
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1682
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1683
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1684
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1685
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1686
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1687
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1688
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1689
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1690
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1691
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1692
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1693
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1694
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1695
end Section14Records_1_1664_1696

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1664_1696


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1696_1728
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_1696_1728
private theorem valid1696 : RecordDataValid section14Catalog 1 (⟨45,(10),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1697 : RecordDataValid section14Catalog 1 (⟨45,(10),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1698 : RecordDataValid section14Catalog 1 (⟨45,(11),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1699 : RecordDataValid section14Catalog 1 (⟨45,(11),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1700 : RecordDataValid section14Catalog 1 (⟨45,(12),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1701 : RecordDataValid section14Catalog 1 (⟨45,(12),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1702 : RecordDataValid section14Catalog 1 (⟨45,(13),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1703 : RecordDataValid section14Catalog 1 (⟨45,(13),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1704 : RecordDataValid section14Catalog 1 (⟨45,(14),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1705 : RecordDataValid section14Catalog 1 (⟨45,(14),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1706 : RecordDataValid section14Catalog 1 (⟨45,(15),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1707 : RecordDataValid section14Catalog 1 (⟨45,(15),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1708 : RecordDataValid section14Catalog 1 (⟨45,(16),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1709 : RecordDataValid section14Catalog 1 (⟨45,(16),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1710 : RecordDataValid section14Catalog 1 (⟨45,(17),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1711 : RecordDataValid section14Catalog 1 (⟨45,(17),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1712 : RecordDataValid section14Catalog 1 (⟨45,(18),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1713 : RecordDataValid section14Catalog 1 (⟨45,(18),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1714 : RecordDataValid section14Catalog 1 (⟨45,(19),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1715 : RecordDataValid section14Catalog 1 (⟨45,(19),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1716 : RecordDataValid section14Catalog 1 (⟨45,(20),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1717 : RecordDataValid section14Catalog 1 (⟨45,(20),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1718 : RecordDataValid section14Catalog 1 (⟨45,(21),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1719 : RecordDataValid section14Catalog 1 (⟨45,(21),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1720 : RecordDataValid section14Catalog 1 (⟨45,(22),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1721 : RecordDataValid section14Catalog 1 (⟨45,(22),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1722 : RecordDataValid section14Catalog 1 (⟨45,(23),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1723 : RecordDataValid section14Catalog 1 (⟨45,(23),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1724 : RecordDataValid section14Catalog 1 (⟨45,(24),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1725 : RecordDataValid section14Catalog 1 (⟨45,(24),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1726 : RecordDataValid section14Catalog 1 (⟨47,(0),[1,2,5,6,13,14],[170,174,190],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1727 : RecordDataValid section14Catalog 1 (⟨47,(0),[1,5,13],[186],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_1696_1728 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1696).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1696).take 32 = [⟨45,(10),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(10),[1,5,13],[186],2⟩,⟨45,(11),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(11),[1,5,13],[186],2⟩,⟨45,(12),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(12),[1,5,13],[186],2⟩,⟨45,(13),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(13),[1,5,13],[186],2⟩,⟨45,(14),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(14),[1,5,13],[186],2⟩,⟨45,(15),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(15),[1,5,13],[186],2⟩,⟨45,(16),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(16),[1,5,13],[186],2⟩,⟨45,(17),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(17),[1,5,13],[186],2⟩,⟨45,(18),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(18),[1,5,13],[186],2⟩,⟨45,(19),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(19),[1,5,13],[186],2⟩,⟨45,(20),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(20),[1,5,13],[186],2⟩,⟨45,(21),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(21),[1,5,13],[186],2⟩,⟨45,(22),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(22),[1,5,13],[186],2⟩,⟨45,(23),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(23),[1,5,13],[186],2⟩,⟨45,(24),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(24),[1,5,13],[186],2⟩,⟨47,(0),[1,2,5,6,13,14],[170,174,190],189⟩,⟨47,(0),[1,5,13],[186],189⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1696
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1697
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1698
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1699
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1700
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1701
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1702
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1703
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1704
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1705
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1706
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1707
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1708
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1709
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1710
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1711
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1712
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1713
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1714
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1715
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1716
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1717
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1718
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1719
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1720
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1721
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1722
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1723
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1724
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1725
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1726
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1727
end Section14Records_1_1696_1728

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1696_1728


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1728_1760
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_1728_1760
private theorem valid1728 : RecordDataValid section14Catalog 1 (⟨47,(1),[1,2,5,6,13,14],[170,174,190],260⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨260,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],261⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1729 : RecordDataValid section14Catalog 1 (⟨47,(1),[1,5,13],[186],260⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨260,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],261⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1730 : RecordDataValid section14Catalog 1 (⟨47,(2),[1,2,5,6,13,14],[170,174,190],261⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨261,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],262⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1731 : RecordDataValid section14Catalog 1 (⟨47,(2),[1,5,13],[186],261⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨261,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],262⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1732 : RecordDataValid section14Catalog 1 (⟨47,(3),[1,2,5,6,13,14],[170,174,190],262⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨262,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],263⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1733 : RecordDataValid section14Catalog 1 (⟨47,(3),[1,5,13],[186],262⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨262,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],263⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1734 : RecordDataValid section14Catalog 1 (⟨47,(4),[1,2,5,6,13,14],[170,174,190],263⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨263,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],264⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1735 : RecordDataValid section14Catalog 1 (⟨47,(4),[1,5,13],[186],263⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨263,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],264⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1736 : RecordDataValid section14Catalog 1 (⟨47,(5),[1,2,5,6,13,14],[170,174,190],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1737 : RecordDataValid section14Catalog 1 (⟨47,(5),[1,5,13],[186],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1738 : RecordDataValid section14Catalog 1 (⟨47,(6),[1,2,5,6,13,14],[170,174,190],260⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨260,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],261⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1739 : RecordDataValid section14Catalog 1 (⟨47,(6),[1,5,13],[186],260⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨260,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],261⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1740 : RecordDataValid section14Catalog 1 (⟨47,(7),[1,2,5,6,13,14],[170],264⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨264,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],265⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1741 : RecordDataValid section14Catalog 1 (⟨47,(7),[1,2,5,6,13,14],[190],319⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨319,[1,2,4,5,6,8,9,10,12,13,14,16],320⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1742 : RecordDataValid section14Catalog 1 (⟨47,(7),[1,2,5,13,14],[174],295⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨295,[1,2,3,5,13,14,15],296⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1743 : RecordDataValid section14Catalog 1 (⟨47,(7),[1,5,13],[186],319⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨319,[1,2,4,5,6,8,9,10,12,13,14,16],320⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1744 : RecordDataValid section14Catalog 1 (⟨47,(8),[1,2,5,6,13,14],[170],265⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨265,[1,2,3,4,5,6,7,10,11,13,14,15,16],266⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1745 : RecordDataValid section14Catalog 1 (⟨47,(8),[1,2,5,6,13,14],[190],320⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨320,[1,2,4,5,6,8,9,10,12,13,14,16],321⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1746 : RecordDataValid section14Catalog 1 (⟨47,(8),[1,2,13,14],[174],296⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨296,[1,2,13,14,15],297⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1747 : RecordDataValid section14Catalog 1 (⟨47,(8),[1,5,13],[186],320⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨320,[1,2,4,5,6,8,9,10,12,13,14,16],321⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1748 : RecordDataValid section14Catalog 1 (⟨47,(9),[1,2,5,6,13,14],[170],266⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨266,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],267⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1749 : RecordDataValid section14Catalog 1 (⟨47,(9),[1,2,5,6,13,14],[190],321⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨321,[1,2,4,5,6,8,9,10,12,13,14,16],322⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1750 : RecordDataValid section14Catalog 1 (⟨47,(9),[1,2,5,13,14],[174],297⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨297,[1,2,3,5,13,14,15],298⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1751 : RecordDataValid section14Catalog 1 (⟨47,(9),[1,5,13],[186],321⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨321,[1,2,4,5,6,8,9,10,12,13,14,16],322⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1752 : RecordDataValid section14Catalog 1 (⟨47,(10),[1,2,5,6,13,14],[170,174,190],194⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨194,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],194⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1753 : RecordDataValid section14Catalog 1 (⟨47,(10),[1,5,13],[186],194⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨194,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],194⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1754 : RecordDataValid section14Catalog 1 (⟨47,(11),[1,2,5,6,13,14],[170,174,190],267⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨267,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],268⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1755 : RecordDataValid section14Catalog 1 (⟨47,(11),[1,5,13],[186],267⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨267,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],268⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1756 : RecordDataValid section14Catalog 1 (⟨47,(12),[1,2,5,6,13,14],[170],268⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨268,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],269⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1757 : RecordDataValid section14Catalog 1 (⟨47,(12),[1,2,5,6,13,14],[190],322⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨322,[1,2,4,5,6,8,9,10,12,13,14,16],323⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1758 : RecordDataValid section14Catalog 1 (⟨47,(12),[1,2,5,13,14],[174],298⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨298,[1,2,3,5,6,7,13,14,15],299⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1759 : RecordDataValid section14Catalog 1 (⟨47,(12),[1,5,13],[186],322⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨322,[1,2,4,5,6,8,9,10,12,13,14,16],323⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_1728_1760 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1728).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1728).take 32 = [⟨47,(1),[1,2,5,6,13,14],[170,174,190],260⟩,⟨47,(1),[1,5,13],[186],260⟩,⟨47,(2),[1,2,5,6,13,14],[170,174,190],261⟩,⟨47,(2),[1,5,13],[186],261⟩,⟨47,(3),[1,2,5,6,13,14],[170,174,190],262⟩,⟨47,(3),[1,5,13],[186],262⟩,⟨47,(4),[1,2,5,6,13,14],[170,174,190],263⟩,⟨47,(4),[1,5,13],[186],263⟩,⟨47,(5),[1,2,5,6,13,14],[170,174,190],189⟩,⟨47,(5),[1,5,13],[186],189⟩,⟨47,(6),[1,2,5,6,13,14],[170,174,190],260⟩,⟨47,(6),[1,5,13],[186],260⟩,⟨47,(7),[1,2,5,6,13,14],[170],264⟩,⟨47,(7),[1,2,5,6,13,14],[190],319⟩,⟨47,(7),[1,2,5,13,14],[174],295⟩,⟨47,(7),[1,5,13],[186],319⟩,⟨47,(8),[1,2,5,6,13,14],[170],265⟩,⟨47,(8),[1,2,5,6,13,14],[190],320⟩,⟨47,(8),[1,2,13,14],[174],296⟩,⟨47,(8),[1,5,13],[186],320⟩,⟨47,(9),[1,2,5,6,13,14],[170],266⟩,⟨47,(9),[1,2,5,6,13,14],[190],321⟩,⟨47,(9),[1,2,5,13,14],[174],297⟩,⟨47,(9),[1,5,13],[186],321⟩,⟨47,(10),[1,2,5,6,13,14],[170,174,190],194⟩,⟨47,(10),[1,5,13],[186],194⟩,⟨47,(11),[1,2,5,6,13,14],[170,174,190],267⟩,⟨47,(11),[1,5,13],[186],267⟩,⟨47,(12),[1,2,5,6,13,14],[170],268⟩,⟨47,(12),[1,2,5,6,13,14],[190],322⟩,⟨47,(12),[1,2,5,13,14],[174],298⟩,⟨47,(12),[1,5,13],[186],322⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1728
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1729
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1730
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1731
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1732
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1733
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1734
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1735
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1736
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1737
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1738
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1739
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1740
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1741
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1742
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1743
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1744
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1745
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1746
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1747
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1748
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1749
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1750
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1751
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1752
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1753
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1754
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1755
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1756
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1757
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1758
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1759
end Section14Records_1_1728_1760

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1728_1760


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1760_1792
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_1760_1792
private theorem valid1760 : RecordDataValid section14Catalog 1 (⟨47,(13),[1,2,5,6,13,14],[170],268⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨268,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],269⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1761 : RecordDataValid section14Catalog 1 (⟨47,(13),[1,2,5,6,13,14],[190],322⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨322,[1,2,4,5,6,8,9,10,12,13,14,16],323⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1762 : RecordDataValid section14Catalog 1 (⟨47,(13),[1,2,5,13,14],[174],298⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨298,[1,2,3,5,6,7,13,14,15],299⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1763 : RecordDataValid section14Catalog 1 (⟨47,(13),[1,5,13],[186],322⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨322,[1,2,4,5,6,8,9,10,12,13,14,16],323⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1764 : RecordDataValid section14Catalog 1 (⟨47,(14),[1,2,5,6,13,14],[170],266⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨266,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],267⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1765 : RecordDataValid section14Catalog 1 (⟨47,(14),[1,2,5,6,13,14],[190],321⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨321,[1,2,4,5,6,8,9,10,12,13,14,16],322⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1766 : RecordDataValid section14Catalog 1 (⟨47,(14),[1,2,5,13,14],[174],297⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨297,[1,2,3,5,13,14,15],298⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1767 : RecordDataValid section14Catalog 1 (⟨47,(14),[1,5,13],[186],321⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨321,[1,2,4,5,6,8,9,10,12,13,14,16],322⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1768 : RecordDataValid section14Catalog 1 (⟨47,(15),[1,2,5,6,13,14],[170,174,190],196⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨196,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],196⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1769 : RecordDataValid section14Catalog 1 (⟨47,(15),[1,5,13],[186],196⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨196,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],196⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1770 : RecordDataValid section14Catalog 1 (⟨47,(16),[1,2,5,6,13,14],[170,174,190],269⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨269,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],270⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1771 : RecordDataValid section14Catalog 1 (⟨47,(16),[1,5,13],[186],269⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨269,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],270⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1772 : RecordDataValid section14Catalog 1 (⟨47,(17),[1,2,5,6,13,14],[170],270⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨270,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],271⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1773 : RecordDataValid section14Catalog 1 (⟨47,(17),[1,2,5,6,13,14],[174],299⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨299,[1,2,3,5,6,7,13,14,15],300⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1774 : RecordDataValid section14Catalog 1 (⟨47,(17),[1,2,5,6,13,14],[190],323⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨323,[1,2,4,5,6,8,9,10,12,13,14,16],324⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1775 : RecordDataValid section14Catalog 1 (⟨47,(17),[1,5,13],[186],323⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨323,[1,2,4,5,6,8,9,10,12,13,14,16],324⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1776 : RecordDataValid section14Catalog 1 (⟨47,(18),[1,2,5,6,13,14],[170],270⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨270,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],271⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1777 : RecordDataValid section14Catalog 1 (⟨47,(18),[1,2,5,6,13,14],[174],299⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨299,[1,2,3,5,6,7,13,14,15],300⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1778 : RecordDataValid section14Catalog 1 (⟨47,(18),[1,2,5,6,13,14],[190],323⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨323,[1,2,4,5,6,8,9,10,12,13,14,16],324⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1779 : RecordDataValid section14Catalog 1 (⟨47,(18),[1,5,13],[186],323⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨323,[1,2,4,5,6,8,9,10,12,13,14,16],324⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1780 : RecordDataValid section14Catalog 1 (⟨47,(19),[1,2,5,6,13,14],[170],270⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨270,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],271⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1781 : RecordDataValid section14Catalog 1 (⟨47,(19),[1,2,5,6,13,14],[174],299⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨299,[1,2,3,5,6,7,13,14,15],300⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1782 : RecordDataValid section14Catalog 1 (⟨47,(19),[1,2,5,6,13,14],[190],323⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨323,[1,2,4,5,6,8,9,10,12,13,14,16],324⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1783 : RecordDataValid section14Catalog 1 (⟨47,(19),[1,5,13],[186],323⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨323,[1,2,4,5,6,8,9,10,12,13,14,16],324⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1784 : RecordDataValid section14Catalog 1 (⟨47,(20),[1,2,5,6,13,14],[170,174,190],198⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨198,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],198⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1785 : RecordDataValid section14Catalog 1 (⟨47,(20),[1,5,13],[186],198⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨198,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],198⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1786 : RecordDataValid section14Catalog 1 (⟨47,(21),[1,2,5,6,13,14],[170,174,190],271⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨271,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],272⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1787 : RecordDataValid section14Catalog 1 (⟨47,(21),[1,5,13],[186],271⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨271,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],272⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1788 : RecordDataValid section14Catalog 1 (⟨47,(22),[1,2,5,6,13,14],[170],272⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨272,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],273⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1789 : RecordDataValid section14Catalog 1 (⟨47,(22),[1,2,5,6,13,14],[174],300⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨300,[1,2,3,5,6,7,13,14,15],301⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1790 : RecordDataValid section14Catalog 1 (⟨47,(22),[1,2,5,6,13,14],[190],324⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨324,[1,2,4,5,6,8,9,10,12,13,14,16],325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1791 : RecordDataValid section14Catalog 1 (⟨47,(22),[1,5,13],[186],324⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨324,[1,2,4,5,6,8,9,10,12,13,14,16],325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_1760_1792 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1760).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1760).take 32 = [⟨47,(13),[1,2,5,6,13,14],[170],268⟩,⟨47,(13),[1,2,5,6,13,14],[190],322⟩,⟨47,(13),[1,2,5,13,14],[174],298⟩,⟨47,(13),[1,5,13],[186],322⟩,⟨47,(14),[1,2,5,6,13,14],[170],266⟩,⟨47,(14),[1,2,5,6,13,14],[190],321⟩,⟨47,(14),[1,2,5,13,14],[174],297⟩,⟨47,(14),[1,5,13],[186],321⟩,⟨47,(15),[1,2,5,6,13,14],[170,174,190],196⟩,⟨47,(15),[1,5,13],[186],196⟩,⟨47,(16),[1,2,5,6,13,14],[170,174,190],269⟩,⟨47,(16),[1,5,13],[186],269⟩,⟨47,(17),[1,2,5,6,13,14],[170],270⟩,⟨47,(17),[1,2,5,6,13,14],[174],299⟩,⟨47,(17),[1,2,5,6,13,14],[190],323⟩,⟨47,(17),[1,5,13],[186],323⟩,⟨47,(18),[1,2,5,6,13,14],[170],270⟩,⟨47,(18),[1,2,5,6,13,14],[174],299⟩,⟨47,(18),[1,2,5,6,13,14],[190],323⟩,⟨47,(18),[1,5,13],[186],323⟩,⟨47,(19),[1,2,5,6,13,14],[170],270⟩,⟨47,(19),[1,2,5,6,13,14],[174],299⟩,⟨47,(19),[1,2,5,6,13,14],[190],323⟩,⟨47,(19),[1,5,13],[186],323⟩,⟨47,(20),[1,2,5,6,13,14],[170,174,190],198⟩,⟨47,(20),[1,5,13],[186],198⟩,⟨47,(21),[1,2,5,6,13,14],[170,174,190],271⟩,⟨47,(21),[1,5,13],[186],271⟩,⟨47,(22),[1,2,5,6,13,14],[170],272⟩,⟨47,(22),[1,2,5,6,13,14],[174],300⟩,⟨47,(22),[1,2,5,6,13,14],[190],324⟩,⟨47,(22),[1,5,13],[186],324⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1760
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1761
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1762
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1763
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1764
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1765
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1766
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1767
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1768
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1769
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1770
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1771
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1772
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1773
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1774
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1775
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1776
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1777
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1778
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1779
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1780
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1781
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1782
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1783
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1784
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1785
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1786
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1787
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1788
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1789
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1790
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1791
end Section14Records_1_1760_1792

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1760_1792

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1664).take 128, section14RecordValid section14Catalog 1 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (1 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 1 r
  exact (all_of_interval_split P xs 1664 1728 1792 (by decide) (by decide) (all_of_interval_split P xs 1664 1696 1728 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_1664_1696 hnum) (Freiman.workReverse20260919_s0001_records_1696_1728 hnum)) (all_of_interval_split P xs 1728 1760 1792 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_1728_1760 hnum) (Freiman.workReverse20260919_s0001_records_1760_1792 hnum)))

#print axioms solution
