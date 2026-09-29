-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_1728_1760
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:20:48.611573+00:00
-- url     : https://prove2.me/submissions/f3b2c854-7b7c-46e2-b528-9c0e7f344f32

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
namespace Section14Records_6_1728_1760
private theorem valid1728 : RecordDataValid section14Catalog 6 (⟨104,(1),[1,5,6,13],[170],434⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨434,[1,4,5,6,8,9,10,12,13,16],435⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1729 : RecordDataValid section14Catalog 6 (⟨104,(2),[1,5,6,13],[170],434⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨434,[1,4,5,6,8,9,10,12,13,16],435⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1730 : RecordDataValid section14Catalog 6 (⟨104,(3),[1,5,6,13],[170],434⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨434,[1,4,5,6,8,9,10,12,13,16],435⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1731 : RecordDataValid section14Catalog 6 (⟨104,(4),[1,5,6,13],[170],434⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨434,[1,4,5,6,8,9,10,12,13,16],435⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1732 : RecordDataValid section14Catalog 6 (⟨104,(5),[1,5,6,13],[170],435⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨435,[1,4,5,6,8,9,10,12,13,16],436⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1733 : RecordDataValid section14Catalog 6 (⟨104,(6),[1,5,6,13],[170],435⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨435,[1,4,5,6,8,9,10,12,13,16],436⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1734 : RecordDataValid section14Catalog 6 (⟨104,(7),[1,5,6,13],[170],435⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨435,[1,4,5,6,8,9,10,12,13,16],436⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1735 : RecordDataValid section14Catalog 6 (⟨104,(8),[1,5,6,13],[170],435⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨435,[1,4,5,6,8,9,10,12,13,16],436⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1736 : RecordDataValid section14Catalog 6 (⟨104,(9),[1,5,6,13],[170],435⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨435,[1,4,5,6,8,9,10,12,13,16],436⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1737 : RecordDataValid section14Catalog 6 (⟨104,(10),[1,5,6,13],[170],436⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨436,[1,4,5,6,8,9,10,12,13,16],437⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1738 : RecordDataValid section14Catalog 6 (⟨104,(11),[1,5,6,13],[170],437⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨437,[1,4,5,6,8,9,10,12,13,16],438⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1739 : RecordDataValid section14Catalog 6 (⟨104,(12),[1,5,6,13],[170],438⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨438,[1,4,5,6,8,9,10,12,13,16],439⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1740 : RecordDataValid section14Catalog 6 (⟨104,(13),[1,5,6,13],[170],437⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨437,[1,4,5,6,8,9,10,12,13,16],438⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1741 : RecordDataValid section14Catalog 6 (⟨104,(14),[1,5,6,13],[170],439⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨439,[1,4,5,6,8,9,10,12,13,16],440⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1742 : RecordDataValid section14Catalog 6 (⟨104,(15),[1,5,6,13],[170],436⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨436,[1,4,5,6,8,9,10,12,13,16],437⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1743 : RecordDataValid section14Catalog 6 (⟨104,(16),[1,5,6,13],[170],440⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨440,[1,4,5,6,8,9,10,12,13,16],441⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1744 : RecordDataValid section14Catalog 6 (⟨104,(17),[1,5,6,13],[170],440⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨440,[1,4,5,6,8,9,10,12,13,16],441⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1745 : RecordDataValid section14Catalog 6 (⟨104,(18),[1,5,6,13],[170],440⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨440,[1,4,5,6,8,9,10,12,13,16],441⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1746 : RecordDataValid section14Catalog 6 (⟨104,(19),[1,5,6,13],[170],440⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨440,[1,4,5,6,8,9,10,12,13,16],441⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1747 : RecordDataValid section14Catalog 6 (⟨104,(20),[1,5,6,13],[170],436⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨436,[1,4,5,6,8,9,10,12,13,16],437⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1748 : RecordDataValid section14Catalog 6 (⟨104,(21),[1,5,6,13],[170],437⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨437,[1,4,5,6,8,9,10,12,13,16],438⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1749 : RecordDataValid section14Catalog 6 (⟨104,(22),[1,5,6,13],[170],438⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨438,[1,4,5,6,8,9,10,12,13,16],439⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1750 : RecordDataValid section14Catalog 6 (⟨104,(23),[1,5,6,13],[170],437⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨437,[1,4,5,6,8,9,10,12,13,16],438⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1751 : RecordDataValid section14Catalog 6 (⟨104,(24),[1,5,6,13],[170],439⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨439,[1,4,5,6,8,9,10,12,13,16],440⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1752 : RecordDataValid section14Catalog 6 (⟨106,(0),[1,5,6,13],[170],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1753 : RecordDataValid section14Catalog 6 (⟨106,(1),[1,5,6,13],[170],442⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨442,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],443⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1754 : RecordDataValid section14Catalog 6 (⟨106,(2),[1,5,6,13],[170],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1755 : RecordDataValid section14Catalog 6 (⟨106,(3),[1,5,6,13],[170],443⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨443,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],444⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1756 : RecordDataValid section14Catalog 6 (⟨106,(4),[1,5,6,13],[170],444⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨444,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],445⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1757 : RecordDataValid section14Catalog 6 (⟨106,(5),[1,5,6,13],[170],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1758 : RecordDataValid section14Catalog 6 (⟨106,(6),[1,5,6,13],[170],442⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨442,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],443⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1759 : RecordDataValid section14Catalog 6 (⟨106,(7),[1,5,6,13],[170],441⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1728).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 1728).take 32 = [⟨104,(1),[1,5,6,13],[170],434⟩,⟨104,(2),[1,5,6,13],[170],434⟩,⟨104,(3),[1,5,6,13],[170],434⟩,⟨104,(4),[1,5,6,13],[170],434⟩,⟨104,(5),[1,5,6,13],[170],435⟩,⟨104,(6),[1,5,6,13],[170],435⟩,⟨104,(7),[1,5,6,13],[170],435⟩,⟨104,(8),[1,5,6,13],[170],435⟩,⟨104,(9),[1,5,6,13],[170],435⟩,⟨104,(10),[1,5,6,13],[170],436⟩,⟨104,(11),[1,5,6,13],[170],437⟩,⟨104,(12),[1,5,6,13],[170],438⟩,⟨104,(13),[1,5,6,13],[170],437⟩,⟨104,(14),[1,5,6,13],[170],439⟩,⟨104,(15),[1,5,6,13],[170],436⟩,⟨104,(16),[1,5,6,13],[170],440⟩,⟨104,(17),[1,5,6,13],[170],440⟩,⟨104,(18),[1,5,6,13],[170],440⟩,⟨104,(19),[1,5,6,13],[170],440⟩,⟨104,(20),[1,5,6,13],[170],436⟩,⟨104,(21),[1,5,6,13],[170],437⟩,⟨104,(22),[1,5,6,13],[170],438⟩,⟨104,(23),[1,5,6,13],[170],437⟩,⟨104,(24),[1,5,6,13],[170],439⟩,⟨106,(0),[1,5,6,13],[170],441⟩,⟨106,(1),[1,5,6,13],[170],442⟩,⟨106,(2),[1,5,6,13],[170],441⟩,⟨106,(3),[1,5,6,13],[170],443⟩,⟨106,(4),[1,5,6,13],[170],444⟩,⟨106,(5),[1,5,6,13],[170],441⟩,⟨106,(6),[1,5,6,13],[170],442⟩,⟨106,(7),[1,5,6,13],[170],441⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1728
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1729
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1730
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1731
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1732
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1733
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1734
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1735
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1736
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1737
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1738
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1739
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1740
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1741
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1742
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1743
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1744
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1745
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1746
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1747
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1748
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1749
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1750
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1751
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1752
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1753
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1754
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1755
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1756
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1757
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1758
  · exact recordValid_of_data section14Catalog 6 _ hnum valid1759
end Section14Records_6_1728_1760

#print axioms solution
