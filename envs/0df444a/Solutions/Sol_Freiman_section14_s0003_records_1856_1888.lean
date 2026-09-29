-- Prove2me | solution 1 for Freiman.section14_s0003_records_1856_1888
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T13:23:03.249349+00:00
-- url     : https://prove2.me/submissions/40f97c81-3a56-4225-a5bf-967e773f79d2

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
namespace Section14Records_3_1856_1888
private theorem valid1856 : RecordDataValid section14Catalog 3 (⟨235,(7),[3,4,7,8,12,15,16],[10],585⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨585,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],586⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1857 : RecordDataValid section14Catalog 3 (⟨235,(7),[3,7],[11],1081⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1081,[3,5,6,7],1085⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1858 : RecordDataValid section14Catalog 3 (⟨235,(8),[3,4,7,8,12,15,16],[10],578⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨578,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],579⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1859 : RecordDataValid section14Catalog 3 (⟨235,(8),[3,7],[11],578⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨578,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],579⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1860 : RecordDataValid section14Catalog 3 (⟨235,(9),[3,4,7,8,12,15,16],[10],579⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨579,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],580⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1861 : RecordDataValid section14Catalog 3 (⟨235,(9),[3,7],[11],579⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨579,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],580⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1862 : RecordDataValid section14Catalog 3 (⟨235,(10),[3,7],[11],1078⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1078,[3,5,6,7],1082⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1863 : RecordDataValid section14Catalog 3 (⟨235,(10),[3,7,15],[10],580⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨580,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],581⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1864 : RecordDataValid section14Catalog 3 (⟨235,(11),[3,4,7,8,12,15,16],[10],581⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨581,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],582⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1865 : RecordDataValid section14Catalog 3 (⟨235,(11),[3,7],[11],1079⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1079,[3,5,6,7],1083⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1866 : RecordDataValid section14Catalog 3 (⟨235,(12),[3,4,7,8,12,15,16],[10],586⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨586,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],587⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1867 : RecordDataValid section14Catalog 3 (⟨235,(12),[3,7],[11],586⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨586,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],587⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1868 : RecordDataValid section14Catalog 3 (⟨235,(13),[3,4,7,8,12,15,16],[10],587⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨587,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],588⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1869 : RecordDataValid section14Catalog 3 (⟨235,(13),[3,7],[11],587⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨587,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],588⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1870 : RecordDataValid section14Catalog 3 (⟨235,(14),[3,7],[11],1082⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1082,[3,5,6,7],1086⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1871 : RecordDataValid section14Catalog 3 (⟨235,(14),[3,7,15],[10],588⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨588,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],589⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1872 : RecordDataValid section14Catalog 3 (⟨235,(15),[3,4,7,8,12,15,16],[10],589⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨589,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],590⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1873 : RecordDataValid section14Catalog 3 (⟨235,(15),[3,7],[11],1083⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1083,[3,5,6,7],1087⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1874 : RecordDataValid section14Catalog 3 (⟨236,(0),[3,4,8,12,15,16],[10],861⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨861,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],862⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1875 : RecordDataValid section14Catalog 3 (⟨236,(0),[3,7],[11],861⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨861,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],862⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1876 : RecordDataValid section14Catalog 3 (⟨236,(1),[3,4,8,12,15,16],[10],862⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨862,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],863⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1877 : RecordDataValid section14Catalog 3 (⟨236,(1),[3,7],[11],862⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨862,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],863⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1878 : RecordDataValid section14Catalog 3 (⟨236,(2),[3,7],[11],863⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨863,[1,2,3,6,7,10,11,13,14,15],864⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1879 : RecordDataValid section14Catalog 3 (⟨236,(2),[3,7,15],[10],863⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨863,[1,2,3,6,7,10,11,13,14,15],864⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1880 : RecordDataValid section14Catalog 3 (⟨236,(3),[3,4,8,12,15,16],[10],864⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨864,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],865⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1881 : RecordDataValid section14Catalog 3 (⟨236,(3),[3,7],[11],864⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨864,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],865⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1882 : RecordDataValid section14Catalog 3 (⟨237,(0),[3,4,8,12,15,16],[10],865⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨865,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],866⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1883 : RecordDataValid section14Catalog 3 (⟨237,(0),[3,7],[11],865⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨865,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],866⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1884 : RecordDataValid section14Catalog 3 (⟨237,(1),[3,4,7,8,15,16],[10],594⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨594,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],595⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1885 : RecordDataValid section14Catalog 3 (⟨237,(1),[3,7],[11],594⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨594,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],595⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1886 : RecordDataValid section14Catalog 3 (⟨237,(2),[3,4,7,8,12,15,16],[10],595⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨595,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],596⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1887 : RecordDataValid section14Catalog 3 (⟨237,(2),[3,7],[11],595⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨595,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],596⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 1856).take 32, section14RecordValid section14Catalog 3 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 1856).take 32 = [⟨235,(7),[3,4,7,8,12,15,16],[10],585⟩,⟨235,(7),[3,7],[11],1081⟩,⟨235,(8),[3,4,7,8,12,15,16],[10],578⟩,⟨235,(8),[3,7],[11],578⟩,⟨235,(9),[3,4,7,8,12,15,16],[10],579⟩,⟨235,(9),[3,7],[11],579⟩,⟨235,(10),[3,7],[11],1078⟩,⟨235,(10),[3,7,15],[10],580⟩,⟨235,(11),[3,4,7,8,12,15,16],[10],581⟩,⟨235,(11),[3,7],[11],1079⟩,⟨235,(12),[3,4,7,8,12,15,16],[10],586⟩,⟨235,(12),[3,7],[11],586⟩,⟨235,(13),[3,4,7,8,12,15,16],[10],587⟩,⟨235,(13),[3,7],[11],587⟩,⟨235,(14),[3,7],[11],1082⟩,⟨235,(14),[3,7,15],[10],588⟩,⟨235,(15),[3,4,7,8,12,15,16],[10],589⟩,⟨235,(15),[3,7],[11],1083⟩,⟨236,(0),[3,4,8,12,15,16],[10],861⟩,⟨236,(0),[3,7],[11],861⟩,⟨236,(1),[3,4,8,12,15,16],[10],862⟩,⟨236,(1),[3,7],[11],862⟩,⟨236,(2),[3,7],[11],863⟩,⟨236,(2),[3,7,15],[10],863⟩,⟨236,(3),[3,4,8,12,15,16],[10],864⟩,⟨236,(3),[3,7],[11],864⟩,⟨237,(0),[3,4,8,12,15,16],[10],865⟩,⟨237,(0),[3,7],[11],865⟩,⟨237,(1),[3,4,7,8,15,16],[10],594⟩,⟨237,(1),[3,7],[11],594⟩,⟨237,(2),[3,4,7,8,12,15,16],[10],595⟩,⟨237,(2),[3,7],[11],595⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1856
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1857
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1858
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1859
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1860
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1861
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1862
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1863
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1864
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1865
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1866
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1867
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1868
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1869
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1870
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1871
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1872
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1873
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1874
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1875
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1876
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1877
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1878
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1879
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1880
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1881
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1882
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1883
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1884
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1885
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1886
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1887
end Section14Records_3_1856_1888

#print axioms solution
