-- Prove2me | solution 1 for Freiman.workReverse20260919_s0001_records_1792_1920
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T01:23:26.631735+00:00
-- url     : https://prove2.me/submissions/da23f5cd-3bd7-49c6-860d-2db17d0cff5a

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1792_1824
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_1792_1824
private theorem valid1792 : RecordDataValid section14Catalog 1 (⟨47,(23),[1,2,5,6,13,14],[170],272⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨272,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],273⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1793 : RecordDataValid section14Catalog 1 (⟨47,(23),[1,2,5,6,13,14],[174],300⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨300,[1,2,3,5,6,7,13,14,15],301⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1794 : RecordDataValid section14Catalog 1 (⟨47,(23),[1,2,5,6,13,14],[190],324⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨324,[1,2,4,5,6,8,9,10,12,13,14,16],325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1795 : RecordDataValid section14Catalog 1 (⟨47,(23),[1,5,13],[186],324⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨324,[1,2,4,5,6,8,9,10,12,13,14,16],325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1796 : RecordDataValid section14Catalog 1 (⟨47,(24),[1,2,5,6,13,14],[170],272⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨272,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],273⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1797 : RecordDataValid section14Catalog 1 (⟨47,(24),[1,2,5,6,13,14],[174],300⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨300,[1,2,3,5,6,7,13,14,15],301⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1798 : RecordDataValid section14Catalog 1 (⟨47,(24),[1,2,5,6,13,14],[190],324⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨324,[1,2,4,5,6,8,9,10,12,13,14,16],325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1799 : RecordDataValid section14Catalog 1 (⟨47,(24),[1,5,13],[186],324⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨324,[1,2,4,5,6,8,9,10,12,13,14,16],325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1800 : RecordDataValid section14Catalog 1 (⟨50,(0),[1,2,5,6],[170],273⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨273,[1,2,5,6],274⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1801 : RecordDataValid section14Catalog 1 (⟨50,(0),[1,2,5,6],[174],301⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨301,[1,2,4,5,6,8,9,10,12],302⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1802 : RecordDataValid section14Catalog 1 (⟨50,(0),[1,2,5,6],[190],331⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨331,[1,2,4,5,6,8,9,10,12],332⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1803 : RecordDataValid section14Catalog 1 (⟨50,(0),[1,5],[186],273⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨273,[1,2,5,6],274⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1804 : RecordDataValid section14Catalog 1 (⟨50,(1),[1,2,5,6],[170],274⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨274,[1,2,5,6],275⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1805 : RecordDataValid section14Catalog 1 (⟨50,(1),[1,2,5,6],[174],302⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨302,[1,2,4,5,6,8,9,10,12],303⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1806 : RecordDataValid section14Catalog 1 (⟨50,(1),[1,2,5,6],[190],332⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨332,[1,2,4,5,6,8,9,10,12],333⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1807 : RecordDataValid section14Catalog 1 (⟨50,(1),[1,5],[186],274⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨274,[1,2,5,6],275⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1808 : RecordDataValid section14Catalog 1 (⟨50,(2),[1,2,5,6],[170],275⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨275,[1,2,5,6],276⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1809 : RecordDataValid section14Catalog 1 (⟨50,(2),[1,2,5,6],[174],303⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨303,[1,2,4,5,6,8,9,10,12],304⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1810 : RecordDataValid section14Catalog 1 (⟨50,(2),[1,2,5,6],[190],333⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨333,[1,2,4,5,6,8,9,10,12],334⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1811 : RecordDataValid section14Catalog 1 (⟨50,(2),[1,5],[186],275⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨275,[1,2,5,6],276⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1812 : RecordDataValid section14Catalog 1 (⟨50,(3),[1,2,5,6],[170],276⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨276,[1,2,5,6],277⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1813 : RecordDataValid section14Catalog 1 (⟨50,(3),[1,2,5,6],[174],304⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨304,[1,2,4,5,6,8,9,10,12],305⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1814 : RecordDataValid section14Catalog 1 (⟨50,(3),[1,2,5,6],[190],334⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨334,[1,2,4,5,6,8,9,10,12],335⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1815 : RecordDataValid section14Catalog 1 (⟨50,(3),[1,5],[186],276⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨276,[1,2,5,6],277⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1816 : RecordDataValid section14Catalog 1 (⟨50,(4),[1,2,5,6],[170],273⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨273,[1,2,5,6],274⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1817 : RecordDataValid section14Catalog 1 (⟨50,(4),[1,2,5,6],[174],301⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨301,[1,2,4,5,6,8,9,10,12],302⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1818 : RecordDataValid section14Catalog 1 (⟨50,(4),[1,2,5,6],[190],331⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨331,[1,2,4,5,6,8,9,10,12],332⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1819 : RecordDataValid section14Catalog 1 (⟨50,(4),[1,5],[186],273⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨273,[1,2,5,6],274⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1820 : RecordDataValid section14Catalog 1 (⟨50,(5),[1,2,5,6],[170],274⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨274,[1,2,5,6],275⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1821 : RecordDataValid section14Catalog 1 (⟨50,(5),[1,2,5,6],[174],302⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨302,[1,2,4,5,6,8,9,10,12],303⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1822 : RecordDataValid section14Catalog 1 (⟨50,(5),[1,2,5,6],[190],332⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨332,[1,2,4,5,6,8,9,10,12],333⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1823 : RecordDataValid section14Catalog 1 (⟨50,(5),[1,5],[186],274⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨274,[1,2,5,6],275⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_1792_1824 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1792).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1792).take 32 = [⟨47,(23),[1,2,5,6,13,14],[170],272⟩,⟨47,(23),[1,2,5,6,13,14],[174],300⟩,⟨47,(23),[1,2,5,6,13,14],[190],324⟩,⟨47,(23),[1,5,13],[186],324⟩,⟨47,(24),[1,2,5,6,13,14],[170],272⟩,⟨47,(24),[1,2,5,6,13,14],[174],300⟩,⟨47,(24),[1,2,5,6,13,14],[190],324⟩,⟨47,(24),[1,5,13],[186],324⟩,⟨50,(0),[1,2,5,6],[170],273⟩,⟨50,(0),[1,2,5,6],[174],301⟩,⟨50,(0),[1,2,5,6],[190],331⟩,⟨50,(0),[1,5],[186],273⟩,⟨50,(1),[1,2,5,6],[170],274⟩,⟨50,(1),[1,2,5,6],[174],302⟩,⟨50,(1),[1,2,5,6],[190],332⟩,⟨50,(1),[1,5],[186],274⟩,⟨50,(2),[1,2,5,6],[170],275⟩,⟨50,(2),[1,2,5,6],[174],303⟩,⟨50,(2),[1,2,5,6],[190],333⟩,⟨50,(2),[1,5],[186],275⟩,⟨50,(3),[1,2,5,6],[170],276⟩,⟨50,(3),[1,2,5,6],[174],304⟩,⟨50,(3),[1,2,5,6],[190],334⟩,⟨50,(3),[1,5],[186],276⟩,⟨50,(4),[1,2,5,6],[170],273⟩,⟨50,(4),[1,2,5,6],[174],301⟩,⟨50,(4),[1,2,5,6],[190],331⟩,⟨50,(4),[1,5],[186],273⟩,⟨50,(5),[1,2,5,6],[170],274⟩,⟨50,(5),[1,2,5,6],[174],302⟩,⟨50,(5),[1,2,5,6],[190],332⟩,⟨50,(5),[1,5],[186],274⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1792
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1793
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1794
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1795
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1796
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1797
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1798
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1799
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1800
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1801
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1802
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1803
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1804
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1805
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1806
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1807
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1808
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1809
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1810
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1811
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1812
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1813
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1814
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1815
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1816
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1817
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1818
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1819
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1820
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1821
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1822
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1823
end Section14Records_1_1792_1824

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1792_1824


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1824_1856
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_1824_1856
private theorem valid1824 : RecordDataValid section14Catalog 1 (⟨50,(6),[1,2,5,6],[170],277⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨277,[1,2,5,6],278⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1825 : RecordDataValid section14Catalog 1 (⟨50,(6),[1,2,5,6],[174],305⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨305,[1,2,4,5,6,8,9,10,12],306⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1826 : RecordDataValid section14Catalog 1 (⟨50,(6),[1,2,5,6],[190],335⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨335,[1,2,4,5,6,8,9,10,12],336⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1827 : RecordDataValid section14Catalog 1 (⟨50,(6),[1,5],[186],277⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨277,[1,2,5,6],278⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1828 : RecordDataValid section14Catalog 1 (⟨50,(7),[1,2,5,6],[170],276⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨276,[1,2,5,6],277⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1829 : RecordDataValid section14Catalog 1 (⟨50,(7),[1,2,5,6],[174],304⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨304,[1,2,4,5,6,8,9,10,12],305⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1830 : RecordDataValid section14Catalog 1 (⟨50,(7),[1,2,5,6],[190],334⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨334,[1,2,4,5,6,8,9,10,12],335⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1831 : RecordDataValid section14Catalog 1 (⟨50,(7),[1,5],[186],276⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨276,[1,2,5,6],277⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1832 : RecordDataValid section14Catalog 1 (⟨50,(8),[1,2,5,6],[170],273⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨273,[1,2,5,6],274⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1833 : RecordDataValid section14Catalog 1 (⟨50,(8),[1,2,5,6],[174],301⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨301,[1,2,4,5,6,8,9,10,12],302⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1834 : RecordDataValid section14Catalog 1 (⟨50,(8),[1,2,5,6],[190],331⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨331,[1,2,4,5,6,8,9,10,12],332⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1835 : RecordDataValid section14Catalog 1 (⟨50,(8),[1,5],[186],273⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨273,[1,2,5,6],274⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1836 : RecordDataValid section14Catalog 1 (⟨50,(9),[1,2,5,6],[170],274⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨274,[1,2,5,6],275⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1837 : RecordDataValid section14Catalog 1 (⟨50,(9),[1,2,5,6],[174],302⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨302,[1,2,4,5,6,8,9,10,12],303⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1838 : RecordDataValid section14Catalog 1 (⟨50,(9),[1,2,5,6],[190],332⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨332,[1,2,4,5,6,8,9,10,12],333⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1839 : RecordDataValid section14Catalog 1 (⟨50,(9),[1,5],[186],274⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨274,[1,2,5,6],275⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1840 : RecordDataValid section14Catalog 1 (⟨50,(10),[1,2,5,6],[170],275⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨275,[1,2,5,6],276⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1841 : RecordDataValid section14Catalog 1 (⟨50,(10),[1,2,5,6],[174],303⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨303,[1,2,4,5,6,8,9,10,12],304⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1842 : RecordDataValid section14Catalog 1 (⟨50,(10),[1,2,5,6],[190],333⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨333,[1,2,4,5,6,8,9,10,12],334⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1843 : RecordDataValid section14Catalog 1 (⟨50,(10),[1,5],[186],275⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨275,[1,2,5,6],276⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1844 : RecordDataValid section14Catalog 1 (⟨50,(11),[1,2,5,6],[170],276⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨276,[1,2,5,6],277⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1845 : RecordDataValid section14Catalog 1 (⟨50,(11),[1,2,5,6],[174],304⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨304,[1,2,4,5,6,8,9,10,12],305⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1846 : RecordDataValid section14Catalog 1 (⟨50,(11),[1,2,5,6],[190],334⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨334,[1,2,4,5,6,8,9,10,12],335⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1847 : RecordDataValid section14Catalog 1 (⟨50,(11),[1,5],[186],276⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨276,[1,2,5,6],277⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1848 : RecordDataValid section14Catalog 1 (⟨50,(12),[1,2,5,6],[170],273⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨273,[1,2,5,6],274⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1849 : RecordDataValid section14Catalog 1 (⟨50,(12),[1,2,5,6],[174],301⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨301,[1,2,4,5,6,8,9,10,12],302⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1850 : RecordDataValid section14Catalog 1 (⟨50,(12),[1,2,5,6],[190],331⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨331,[1,2,4,5,6,8,9,10,12],332⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1851 : RecordDataValid section14Catalog 1 (⟨50,(12),[1,5],[186],273⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨273,[1,2,5,6],274⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1852 : RecordDataValid section14Catalog 1 (⟨50,(13),[1,2,5,6],[170],274⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨274,[1,2,5,6],275⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1853 : RecordDataValid section14Catalog 1 (⟨50,(13),[1,2,5,6],[174],302⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨302,[1,2,4,5,6,8,9,10,12],303⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1854 : RecordDataValid section14Catalog 1 (⟨50,(13),[1,2,5,6],[190],332⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨332,[1,2,4,5,6,8,9,10,12],333⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1855 : RecordDataValid section14Catalog 1 (⟨50,(13),[1,5],[186],274⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨274,[1,2,5,6],275⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_1824_1856 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1824).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1824).take 32 = [⟨50,(6),[1,2,5,6],[170],277⟩,⟨50,(6),[1,2,5,6],[174],305⟩,⟨50,(6),[1,2,5,6],[190],335⟩,⟨50,(6),[1,5],[186],277⟩,⟨50,(7),[1,2,5,6],[170],276⟩,⟨50,(7),[1,2,5,6],[174],304⟩,⟨50,(7),[1,2,5,6],[190],334⟩,⟨50,(7),[1,5],[186],276⟩,⟨50,(8),[1,2,5,6],[170],273⟩,⟨50,(8),[1,2,5,6],[174],301⟩,⟨50,(8),[1,2,5,6],[190],331⟩,⟨50,(8),[1,5],[186],273⟩,⟨50,(9),[1,2,5,6],[170],274⟩,⟨50,(9),[1,2,5,6],[174],302⟩,⟨50,(9),[1,2,5,6],[190],332⟩,⟨50,(9),[1,5],[186],274⟩,⟨50,(10),[1,2,5,6],[170],275⟩,⟨50,(10),[1,2,5,6],[174],303⟩,⟨50,(10),[1,2,5,6],[190],333⟩,⟨50,(10),[1,5],[186],275⟩,⟨50,(11),[1,2,5,6],[170],276⟩,⟨50,(11),[1,2,5,6],[174],304⟩,⟨50,(11),[1,2,5,6],[190],334⟩,⟨50,(11),[1,5],[186],276⟩,⟨50,(12),[1,2,5,6],[170],273⟩,⟨50,(12),[1,2,5,6],[174],301⟩,⟨50,(12),[1,2,5,6],[190],331⟩,⟨50,(12),[1,5],[186],273⟩,⟨50,(13),[1,2,5,6],[170],274⟩,⟨50,(13),[1,2,5,6],[174],302⟩,⟨50,(13),[1,2,5,6],[190],332⟩,⟨50,(13),[1,5],[186],274⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1824
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1825
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1826
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1827
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1828
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1829
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1830
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1831
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1832
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1833
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1834
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1835
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1836
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1837
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1838
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1839
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1840
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1841
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1842
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1843
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1844
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1845
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1846
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1847
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1848
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1849
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1850
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1851
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1852
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1853
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1854
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1855
end Section14Records_1_1824_1856

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1824_1856


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1856_1888
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_1856_1888
private theorem valid1856 : RecordDataValid section14Catalog 1 (⟨50,(14),[1,2,5,6],[170],278⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨278,[1,2,5,6],279⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1857 : RecordDataValid section14Catalog 1 (⟨50,(14),[1,2,5,6],[174],306⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨306,[1,2,4,5,6,8,9,10,12],307⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1858 : RecordDataValid section14Catalog 1 (⟨50,(14),[1,2,5,6],[190],336⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨336,[1,2,4,5,6,8,9,10,12],337⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1859 : RecordDataValid section14Catalog 1 (⟨50,(14),[1,5],[186],278⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨278,[1,2,5,6],279⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1860 : RecordDataValid section14Catalog 1 (⟨50,(15),[1,2,5,6],[170],276⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨276,[1,2,5,6],277⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1861 : RecordDataValid section14Catalog 1 (⟨50,(15),[1,2,5,6],[174],304⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨304,[1,2,4,5,6,8,9,10,12],305⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1862 : RecordDataValid section14Catalog 1 (⟨50,(15),[1,2,5,6],[190],334⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨334,[1,2,4,5,6,8,9,10,12],335⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1863 : RecordDataValid section14Catalog 1 (⟨50,(15),[1,5],[186],276⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨276,[1,2,5,6],277⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1864 : RecordDataValid section14Catalog 1 (⟨53,(0),[1,2],[174],307⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨307,[1,2,3,5,6,7],308⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1865 : RecordDataValid section14Catalog 1 (⟨53,(0),[1,2,5,6],[170],279⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨279,[1,2,3,4,5,6,7,8,9,10,11,12],280⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1866 : RecordDataValid section14Catalog 1 (⟨53,(0),[1,2,5,6],[190],325⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨325,[1,2,4,5,6,8,9,10,12],326⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1867 : RecordDataValid section14Catalog 1 (⟨53,(0),[1,5],[186],325⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨325,[1,2,4,5,6,8,9,10,12],326⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1868 : RecordDataValid section14Catalog 1 (⟨53,(1),[1,2,5],[174],308⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨308,[1,2,3,5,6,7],309⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1869 : RecordDataValid section14Catalog 1 (⟨53,(1),[1,2,5,6],[170],280⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨280,[1,2,3,4,5,6,7,8,9,10,11,12],281⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1870 : RecordDataValid section14Catalog 1 (⟨53,(1),[1,2,5,6],[190],326⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨326,[1,2,4,5,6,8,9,10,12],327⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1871 : RecordDataValid section14Catalog 1 (⟨53,(1),[1,5],[186],326⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨326,[1,2,4,5,6,8,9,10,12],327⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1872 : RecordDataValid section14Catalog 1 (⟨53,(2),[1,2,5,6],[170],281⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨281,[1,2,3,4,5,6,7,8,9,10,11,12],282⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1873 : RecordDataValid section14Catalog 1 (⟨53,(2),[1,2,5,6],[174],309⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨309,[1,2,3,5,6,7],310⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1874 : RecordDataValid section14Catalog 1 (⟨53,(2),[1,2,5,6],[190],327⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨327,[1,2,4,5,6,8,9,10,12],328⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1875 : RecordDataValid section14Catalog 1 (⟨53,(2),[1,5],[186],327⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨327,[1,2,4,5,6,8,9,10,12],328⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1876 : RecordDataValid section14Catalog 1 (⟨53,(3),[1,2,5],[174],310⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨310,[1,2,3,5,6,7],311⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1877 : RecordDataValid section14Catalog 1 (⟨53,(3),[1,2,5,6],[170],282⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨282,[1,2,3,4,5,6,7,8,9,10,11,12],283⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1878 : RecordDataValid section14Catalog 1 (⟨53,(3),[1,2,5,6],[190],328⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨328,[1,2,4,5,6,8,9,10,12],329⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1879 : RecordDataValid section14Catalog 1 (⟨53,(3),[1,5],[186],328⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨328,[1,2,4,5,6,8,9,10,12],329⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1880 : RecordDataValid section14Catalog 1 (⟨55,(0),[1,5],[170,174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1881 : RecordDataValid section14Catalog 1 (⟨55,(0),[1,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1882 : RecordDataValid section14Catalog 1 (⟨55,(0),[1,5,13],[186],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1883 : RecordDataValid section14Catalog 1 (⟨55,(1),[1,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1884 : RecordDataValid section14Catalog 1 (⟨55,(1),[1,5,13],[186],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1885 : RecordDataValid section14Catalog 1 (⟨55,(2),[1,2,5,6,14],[170,174],97⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨97,[1,2,5,6,9,10,13,14],97⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1886 : RecordDataValid section14Catalog 1 (⟨55,(2),[1,2,5,14],[190],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1887 : RecordDataValid section14Catalog 1 (⟨55,(2),[1,5],[186],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_1856_1888 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1856).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1856).take 32 = [⟨50,(14),[1,2,5,6],[170],278⟩,⟨50,(14),[1,2,5,6],[174],306⟩,⟨50,(14),[1,2,5,6],[190],336⟩,⟨50,(14),[1,5],[186],278⟩,⟨50,(15),[1,2,5,6],[170],276⟩,⟨50,(15),[1,2,5,6],[174],304⟩,⟨50,(15),[1,2,5,6],[190],334⟩,⟨50,(15),[1,5],[186],276⟩,⟨53,(0),[1,2],[174],307⟩,⟨53,(0),[1,2,5,6],[170],279⟩,⟨53,(0),[1,2,5,6],[190],325⟩,⟨53,(0),[1,5],[186],325⟩,⟨53,(1),[1,2,5],[174],308⟩,⟨53,(1),[1,2,5,6],[170],280⟩,⟨53,(1),[1,2,5,6],[190],326⟩,⟨53,(1),[1,5],[186],326⟩,⟨53,(2),[1,2,5,6],[170],281⟩,⟨53,(2),[1,2,5,6],[174],309⟩,⟨53,(2),[1,2,5,6],[190],327⟩,⟨53,(2),[1,5],[186],327⟩,⟨53,(3),[1,2,5],[174],310⟩,⟨53,(3),[1,2,5,6],[170],282⟩,⟨53,(3),[1,2,5,6],[190],328⟩,⟨53,(3),[1,5],[186],328⟩,⟨55,(0),[1,5],[170,174],3⟩,⟨55,(0),[1,5,6,13,14],[190],3⟩,⟨55,(0),[1,5,13],[186],3⟩,⟨55,(1),[1,5,6,13,14],[170,174,190],3⟩,⟨55,(1),[1,5,13],[186],3⟩,⟨55,(2),[1,2,5,6,14],[170,174],97⟩,⟨55,(2),[1,2,5,14],[190],29⟩,⟨55,(2),[1,5],[186],29⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1856
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1857
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1858
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1859
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1860
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1861
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1862
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1863
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1864
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1865
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1866
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1867
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1868
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1869
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1870
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1871
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1872
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1873
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1874
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1875
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1876
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1877
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1878
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1879
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1880
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1881
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1882
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1883
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1884
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1885
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1886
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1887
end Section14Records_1_1856_1888

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1856_1888


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1888_1920
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_1888_1920
private theorem valid1888 : RecordDataValid section14Catalog 1 (⟨55,(3),[1,2,5,6,14],[190],234⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨234,[1,2,5,6,9,10,13,14],234⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1889 : RecordDataValid section14Catalog 1 (⟨55,(3),[1,5],[186],234⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨234,[1,2,5,6,9,10,13,14],234⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1890 : RecordDataValid section14Catalog 1 (⟨55,(3),[1,6,13],[170,174],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1891 : RecordDataValid section14Catalog 1 (⟨55,(4),[1,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1892 : RecordDataValid section14Catalog 1 (⟨55,(4),[1,5,13],[186],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1893 : RecordDataValid section14Catalog 1 (⟨55,(5),[1,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1894 : RecordDataValid section14Catalog 1 (⟨55,(5),[1,5,13],[186],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1895 : RecordDataValid section14Catalog 1 (⟨55,(6),[1,2,5,6,13,14],[170,174],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1896 : RecordDataValid section14Catalog 1 (⟨55,(6),[1,2,5,14],[190],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1897 : RecordDataValid section14Catalog 1 (⟨55,(6),[1,5],[186],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1898 : RecordDataValid section14Catalog 1 (⟨55,(7),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1899 : RecordDataValid section14Catalog 1 (⟨55,(7),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1900 : RecordDataValid section14Catalog 1 (⟨55,(7),[1,6,13],[170,174],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1901 : RecordDataValid section14Catalog 1 (⟨55,(8),[1,2],[170,174],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1902 : RecordDataValid section14Catalog 1 (⟨55,(8),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1903 : RecordDataValid section14Catalog 1 (⟨55,(8),[1,5,13],[186],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1904 : RecordDataValid section14Catalog 1 (⟨55,(9),[1,2,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1905 : RecordDataValid section14Catalog 1 (⟨55,(9),[1,5,13],[186],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1906 : RecordDataValid section14Catalog 1 (⟨55,(10),[1,2,5,6,13,14],[190],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1907 : RecordDataValid section14Catalog 1 (⟨55,(10),[1,2,5,6,13,14],[170,174],97⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨97,[1,2,5,6,9,10,13,14],97⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1908 : RecordDataValid section14Catalog 1 (⟨55,(10),[1,5,13],[186],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1909 : RecordDataValid section14Catalog 1 (⟨55,(11),[1,2,5,6,13,14],[170,174],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1910 : RecordDataValid section14Catalog 1 (⟨55,(11),[1,2,5,6,13,14],[190],234⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨234,[1,2,5,6,9,10,13,14],234⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1911 : RecordDataValid section14Catalog 1 (⟨55,(11),[1,5,13],[186],234⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨234,[1,2,5,6,9,10,13,14],234⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1912 : RecordDataValid section14Catalog 1 (⟨55,(12),[1],[186],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1913 : RecordDataValid section14Catalog 1 (⟨55,(12),[1,2,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1914 : RecordDataValid section14Catalog 1 (⟨55,(13),[1],[186],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1915 : RecordDataValid section14Catalog 1 (⟨55,(13),[1,2,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1916 : RecordDataValid section14Catalog 1 (⟨55,(14),[1,2,5,6,13],[190],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1917 : RecordDataValid section14Catalog 1 (⟨55,(14),[1,2,5,6,13,14],[170,174],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1918 : RecordDataValid section14Catalog 1 (⟨55,(14),[1,5,13],[186],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1919 : RecordDataValid section14Catalog 1 (⟨55,(15),[1,2,5,6,13],[170,174],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_1888_1920 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1888).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1888).take 32 = [⟨55,(3),[1,2,5,6,14],[190],234⟩,⟨55,(3),[1,5],[186],234⟩,⟨55,(3),[1,6,13],[170,174],2⟩,⟨55,(4),[1,5,6,13,14],[170,174,190],3⟩,⟨55,(4),[1,5,13],[186],3⟩,⟨55,(5),[1,5,6,13,14],[170,174,190],3⟩,⟨55,(5),[1,5,13],[186],3⟩,⟨55,(6),[1,2,5,6,13,14],[170,174],2⟩,⟨55,(6),[1,2,5,14],[190],29⟩,⟨55,(6),[1,5],[186],29⟩,⟨55,(7),[1,2,5,6,13,14],[190],2⟩,⟨55,(7),[1,5,13],[186],2⟩,⟨55,(7),[1,6,13],[170,174],2⟩,⟨55,(8),[1,2],[170,174],3⟩,⟨55,(8),[1,2,5,6,13,14],[190],3⟩,⟨55,(8),[1,5,13],[186],3⟩,⟨55,(9),[1,2,5,6,13,14],[170,174,190],3⟩,⟨55,(9),[1,5,13],[186],3⟩,⟨55,(10),[1,2,5,6,13,14],[190],29⟩,⟨55,(10),[1,2,5,6,13,14],[170,174],97⟩,⟨55,(10),[1,5,13],[186],29⟩,⟨55,(11),[1,2,5,6,13,14],[170,174],29⟩,⟨55,(11),[1,2,5,6,13,14],[190],234⟩,⟨55,(11),[1,5,13],[186],234⟩,⟨55,(12),[1],[186],3⟩,⟨55,(12),[1,2,14],[170,174,190],3⟩,⟨55,(13),[1],[186],3⟩,⟨55,(13),[1,2,14],[170,174,190],3⟩,⟨55,(14),[1,2,5,6,13],[190],99⟩,⟨55,(14),[1,2,5,6,13,14],[170,174],99⟩,⟨55,(14),[1,5,13],[186],99⟩,⟨55,(15),[1,2,5,6,13],[170,174],99⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1888
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1889
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1890
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1891
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1892
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1893
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1894
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1895
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1896
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1897
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1898
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1899
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1900
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1901
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1902
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1903
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1904
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1905
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1906
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1907
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1908
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1909
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1910
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1911
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1912
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1913
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1914
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1915
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1916
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1917
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1918
  · exact recordValid_of_data section14Catalog 1 _ hnum valid1919
end Section14Records_1_1888_1920

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_1888_1920

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 1792).take 128, section14RecordValid section14Catalog 1 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (1 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 1 r
  exact (all_of_interval_split P xs 1792 1856 1920 (by decide) (by decide) (all_of_interval_split P xs 1792 1824 1856 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_1792_1824 hnum) (Freiman.workReverse20260919_s0001_records_1824_1856 hnum)) (all_of_interval_split P xs 1856 1888 1920 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_1856_1888 hnum) (Freiman.workReverse20260919_s0001_records_1888_1920 hnum)))

#print axioms solution
