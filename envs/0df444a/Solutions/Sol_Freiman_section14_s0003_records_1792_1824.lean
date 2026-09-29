-- Prove2me | solution 1 for Freiman.section14_s0003_records_1792_1824
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T13:17:59.412454+00:00
-- url     : https://prove2.me/submissions/11a9c174-4347-4688-8c16-73d90ece37d0

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
namespace Section14Records_3_1792_1824
private theorem valid1792 : RecordDataValid section14Catalog 3 (⟨232,(11),[3,4,7,8,12,15,16],[10],854⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨854,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],855⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1793 : RecordDataValid section14Catalog 3 (⟨232,(11),[3,7],[11],854⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨854,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],855⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1794 : RecordDataValid section14Catalog 3 (⟨232,(12),[3],[11],1069⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1069,[3,5,6,7],1073⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1795 : RecordDataValid section14Catalog 3 (⟨232,(12),[3,4,7,8,12,15,16],[10],846⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨846,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],847⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1796 : RecordDataValid section14Catalog 3 (⟨232,(13),[3,4,7,8,12,15,16],[10],847⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨847,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],848⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1797 : RecordDataValid section14Catalog 3 (⟨232,(13),[3,7],[11],847⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨847,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],848⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1798 : RecordDataValid section14Catalog 3 (⟨232,(14),[3,7],[11],1069⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1069,[3,5,6,7],1073⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1799 : RecordDataValid section14Catalog 3 (⟨232,(14),[3,7,15],[10],855⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨855,[1,2,3,5,6,7,10,11,13,14,15],856⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1800 : RecordDataValid section14Catalog 3 (⟨232,(15),[3,4,7,8,12,15,16],[10],856⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨856,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],857⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1801 : RecordDataValid section14Catalog 3 (⟨232,(15),[3,7],[11],856⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨856,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],857⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1802 : RecordDataValid section14Catalog 3 (⟨232,(16),[3,4,7,8,12,15,16],[10],857⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨857,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],858⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1803 : RecordDataValid section14Catalog 3 (⟨232,(16),[3,7],[11],857⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨857,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],858⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1804 : RecordDataValid section14Catalog 3 (⟨232,(17),[3],[11],1071⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1071,[3,5,6,7],1075⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1805 : RecordDataValid section14Catalog 3 (⟨232,(17),[3,4,7,8,12,15,16],[10],858⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨858,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],859⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1806 : RecordDataValid section14Catalog 3 (⟨232,(18),[3,4,7,8,12,15,16],[10],859⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨859,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],860⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1807 : RecordDataValid section14Catalog 3 (⟨232,(18),[3,7],[11],859⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨859,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],860⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1808 : RecordDataValid section14Catalog 3 (⟨232,(19),[3,7],[11],1071⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1071,[3,5,6,7],1075⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1809 : RecordDataValid section14Catalog 3 (⟨232,(19),[3,7,15],[10],860⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨860,[1,2,3,5,6,7,10,11,13,14,15],861⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1810 : RecordDataValid section14Catalog 3 (⟨234,(0),[3,4,7,8,12,15,16],[10],568⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨568,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],569⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1811 : RecordDataValid section14Catalog 3 (⟨234,(0),[3,7],[11],1072⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1072,[3,5,6,7],1076⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1812 : RecordDataValid section14Catalog 3 (⟨234,(1),[3,7],[11],1073⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1073,[3,5,6,7],1077⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1813 : RecordDataValid section14Catalog 3 (⟨234,(1),[3,7,15],[10],569⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨569,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],570⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1814 : RecordDataValid section14Catalog 3 (⟨234,(2),[3,7],[11],1072⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1072,[3,5,6,7],1076⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1815 : RecordDataValid section14Catalog 3 (⟨234,(2),[3,7,15],[10],570⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨570,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],571⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1816 : RecordDataValid section14Catalog 3 (⟨234,(3),[3,7],[11],1074⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1074,[3,5,6,7],1078⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1817 : RecordDataValid section14Catalog 3 (⟨234,(3),[3,7,15],[10],571⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨571,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],572⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1818 : RecordDataValid section14Catalog 3 (⟨234,(4),[3,4,7,8,12,15,16],[10],572⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨572,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],573⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1819 : RecordDataValid section14Catalog 3 (⟨234,(4),[3,7],[11],1075⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1075,[3,5,6,7],1079⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1820 : RecordDataValid section14Catalog 3 (⟨234,(5),[3,7],[11],1075⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1075,[3,5,6,7],1079⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1821 : RecordDataValid section14Catalog 3 (⟨234,(5),[3,7,15],[10],573⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨573,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],574⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1822 : RecordDataValid section14Catalog 3 (⟨234,(6),[3,7],[11],1075⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1075,[3,5,6,7],1079⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1823 : RecordDataValid section14Catalog 3 (⟨234,(6),[3,7,15],[10],573⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨573,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],574⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 1792).take 32, section14RecordValid section14Catalog 3 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 1792).take 32 = [⟨232,(11),[3,4,7,8,12,15,16],[10],854⟩,⟨232,(11),[3,7],[11],854⟩,⟨232,(12),[3],[11],1069⟩,⟨232,(12),[3,4,7,8,12,15,16],[10],846⟩,⟨232,(13),[3,4,7,8,12,15,16],[10],847⟩,⟨232,(13),[3,7],[11],847⟩,⟨232,(14),[3,7],[11],1069⟩,⟨232,(14),[3,7,15],[10],855⟩,⟨232,(15),[3,4,7,8,12,15,16],[10],856⟩,⟨232,(15),[3,7],[11],856⟩,⟨232,(16),[3,4,7,8,12,15,16],[10],857⟩,⟨232,(16),[3,7],[11],857⟩,⟨232,(17),[3],[11],1071⟩,⟨232,(17),[3,4,7,8,12,15,16],[10],858⟩,⟨232,(18),[3,4,7,8,12,15,16],[10],859⟩,⟨232,(18),[3,7],[11],859⟩,⟨232,(19),[3,7],[11],1071⟩,⟨232,(19),[3,7,15],[10],860⟩,⟨234,(0),[3,4,7,8,12,15,16],[10],568⟩,⟨234,(0),[3,7],[11],1072⟩,⟨234,(1),[3,7],[11],1073⟩,⟨234,(1),[3,7,15],[10],569⟩,⟨234,(2),[3,7],[11],1072⟩,⟨234,(2),[3,7,15],[10],570⟩,⟨234,(3),[3,7],[11],1074⟩,⟨234,(3),[3,7,15],[10],571⟩,⟨234,(4),[3,4,7,8,12,15,16],[10],572⟩,⟨234,(4),[3,7],[11],1075⟩,⟨234,(5),[3,7],[11],1075⟩,⟨234,(5),[3,7,15],[10],573⟩,⟨234,(6),[3,7],[11],1075⟩,⟨234,(6),[3,7,15],[10],573⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1792
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1793
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1794
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1795
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1796
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1797
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1798
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1799
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1800
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1801
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1802
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1803
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1804
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1805
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1806
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1807
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1808
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1809
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1810
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1811
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1812
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1813
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1814
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1815
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1816
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1817
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1818
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1819
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1820
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1821
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1822
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1823
end Section14Records_3_1792_1824

#print axioms solution
