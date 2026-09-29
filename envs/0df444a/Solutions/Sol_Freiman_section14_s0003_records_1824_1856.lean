-- Prove2me | solution 1 for Freiman.section14_s0003_records_1824_1856
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T13:20:52.301319+00:00
-- url     : https://prove2.me/submissions/3cde1bdf-bc53-4de8-b4dd-477f8716df5a

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
namespace Section14Records_3_1824_1856
private theorem valid1824 : RecordDataValid section14Catalog 3 (⟨234,(7),[3,7],[11],1075⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1075,[3,5,6,7],1079⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1825 : RecordDataValid section14Catalog 3 (⟨234,(7),[3,7,15],[10],573⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨573,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],574⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1826 : RecordDataValid section14Catalog 3 (⟨234,(8),[3,4,7,8,12,15,16],[10],574⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨574,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],575⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1827 : RecordDataValid section14Catalog 3 (⟨234,(8),[3,7],[11],1076⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1076,[3,5,6,7],1080⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1828 : RecordDataValid section14Catalog 3 (⟨234,(9),[3,7],[11],1076⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1076,[3,5,6,7],1080⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1829 : RecordDataValid section14Catalog 3 (⟨234,(9),[3,7,15],[10],575⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨575,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],576⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1830 : RecordDataValid section14Catalog 3 (⟨234,(10),[3,7],[11],1076⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1076,[3,5,6,7],1080⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1831 : RecordDataValid section14Catalog 3 (⟨234,(10),[3,7,15],[10],575⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨575,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],576⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1832 : RecordDataValid section14Catalog 3 (⟨234,(11),[3,7],[11],1076⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1076,[3,5,6,7],1080⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1833 : RecordDataValid section14Catalog 3 (⟨234,(11),[3,7,15],[10],575⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨575,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],576⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1834 : RecordDataValid section14Catalog 3 (⟨234,(12),[3,4,7,8,12,15,16],[10],576⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨576,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],577⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1835 : RecordDataValid section14Catalog 3 (⟨234,(12),[3,7],[11],1077⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1077,[3,5,6,7],1081⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1836 : RecordDataValid section14Catalog 3 (⟨234,(13),[3,7],[11],1077⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1077,[3,5,6,7],1081⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1837 : RecordDataValid section14Catalog 3 (⟨234,(13),[3,7,15],[10],577⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1838 : RecordDataValid section14Catalog 3 (⟨234,(14),[3,7],[11],1077⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1077,[3,5,6,7],1081⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1839 : RecordDataValid section14Catalog 3 (⟨234,(14),[3,7,15],[10],577⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1840 : RecordDataValid section14Catalog 3 (⟨234,(15),[3,7],[11],1077⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1077,[3,5,6,7],1081⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1841 : RecordDataValid section14Catalog 3 (⟨234,(15),[3,7,15],[10],577⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1842 : RecordDataValid section14Catalog 3 (⟨235,(0),[3,4,7,8,12,15,16],[10],578⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨578,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],579⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1843 : RecordDataValid section14Catalog 3 (⟨235,(0),[3,7],[11],578⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨578,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],579⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1844 : RecordDataValid section14Catalog 3 (⟨235,(1),[3,4,7,8,12,15,16],[10],579⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨579,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],580⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1845 : RecordDataValid section14Catalog 3 (⟨235,(1),[3,7],[11],579⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨579,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],580⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1846 : RecordDataValid section14Catalog 3 (⟨235,(2),[3,7],[11],1078⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1078,[3,5,6,7],1082⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1847 : RecordDataValid section14Catalog 3 (⟨235,(2),[3,7,15],[10],580⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨580,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],581⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1848 : RecordDataValid section14Catalog 3 (⟨235,(3),[3,4,7,8,12,15,16],[10],581⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨581,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],582⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1849 : RecordDataValid section14Catalog 3 (⟨235,(3),[3,7],[11],1079⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1079,[3,5,6,7],1083⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1850 : RecordDataValid section14Catalog 3 (⟨235,(4),[3,4,7,8,12,15,16],[10],582⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨582,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],583⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1851 : RecordDataValid section14Catalog 3 (⟨235,(4),[3,7],[11],582⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨582,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],583⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1852 : RecordDataValid section14Catalog 3 (⟨235,(5),[3,4,7,8,12,15,16],[10],583⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨583,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],584⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1853 : RecordDataValid section14Catalog 3 (⟨235,(5),[3,7],[11],583⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨583,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],584⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1854 : RecordDataValid section14Catalog 3 (⟨235,(6),[3,7],[11],1080⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1080,[3,5,6,7],1084⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1855 : RecordDataValid section14Catalog 3 (⟨235,(6),[3,7,15],[10],584⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨584,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],585⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 1824).take 32, section14RecordValid section14Catalog 3 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 1824).take 32 = [⟨234,(7),[3,7],[11],1075⟩,⟨234,(7),[3,7,15],[10],573⟩,⟨234,(8),[3,4,7,8,12,15,16],[10],574⟩,⟨234,(8),[3,7],[11],1076⟩,⟨234,(9),[3,7],[11],1076⟩,⟨234,(9),[3,7,15],[10],575⟩,⟨234,(10),[3,7],[11],1076⟩,⟨234,(10),[3,7,15],[10],575⟩,⟨234,(11),[3,7],[11],1076⟩,⟨234,(11),[3,7,15],[10],575⟩,⟨234,(12),[3,4,7,8,12,15,16],[10],576⟩,⟨234,(12),[3,7],[11],1077⟩,⟨234,(13),[3,7],[11],1077⟩,⟨234,(13),[3,7,15],[10],577⟩,⟨234,(14),[3,7],[11],1077⟩,⟨234,(14),[3,7,15],[10],577⟩,⟨234,(15),[3,7],[11],1077⟩,⟨234,(15),[3,7,15],[10],577⟩,⟨235,(0),[3,4,7,8,12,15,16],[10],578⟩,⟨235,(0),[3,7],[11],578⟩,⟨235,(1),[3,4,7,8,12,15,16],[10],579⟩,⟨235,(1),[3,7],[11],579⟩,⟨235,(2),[3,7],[11],1078⟩,⟨235,(2),[3,7,15],[10],580⟩,⟨235,(3),[3,4,7,8,12,15,16],[10],581⟩,⟨235,(3),[3,7],[11],1079⟩,⟨235,(4),[3,4,7,8,12,15,16],[10],582⟩,⟨235,(4),[3,7],[11],582⟩,⟨235,(5),[3,4,7,8,12,15,16],[10],583⟩,⟨235,(5),[3,7],[11],583⟩,⟨235,(6),[3,7],[11],1080⟩,⟨235,(6),[3,7,15],[10],584⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1824
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1825
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1826
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1827
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1828
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1829
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1830
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1831
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1832
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1833
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1834
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1835
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1836
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1837
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1838
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1839
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1840
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1841
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1842
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1843
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1844
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1845
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1846
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1847
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1848
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1849
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1850
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1851
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1852
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1853
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1854
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1855
end Section14Records_3_1824_1856

#print axioms solution
