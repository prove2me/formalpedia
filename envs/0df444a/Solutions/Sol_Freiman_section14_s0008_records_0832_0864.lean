-- Prove2me | solution 1 for Freiman.section14_s0008_records_0832_0864
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T07:09:48.233003+00:00
-- url     : https://prove2.me/submissions/320244d4-1ba9-4b2c-beb9-6243eb13c50c

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
namespace Section14Records_8_832_864
private theorem valid832 : RecordDataValid section14Catalog 8 (⟨124,(9),[4,8,12,16],[10],489⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨489,[1,4,5,6,8,9,10,12,13,16],490⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid833 : RecordDataValid section14Catalog 8 (⟨124,(10),[4,8,12,16],[10],490⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨490,[1,4,5,6,8,9,10,12,13,16],491⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid834 : RecordDataValid section14Catalog 8 (⟨124,(11),[4,8,12,16],[10],491⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨491,[1,4,5,6,8,9,10,12,13,16],492⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid835 : RecordDataValid section14Catalog 8 (⟨124,(12),[4,8,12,16],[10],488⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨488,[1,4,5,6,8,9,10,12,13,16],489⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid836 : RecordDataValid section14Catalog 8 (⟨124,(13),[4,8,12,16],[10],489⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨489,[1,4,5,6,8,9,10,12,13,16],490⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid837 : RecordDataValid section14Catalog 8 (⟨124,(14),[4,8,12,16],[10],493⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨493,[1,4,5,6,8,9,10,12,13,16],494⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid838 : RecordDataValid section14Catalog 8 (⟨124,(15),[4,8,12,16],[10],491⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨491,[1,4,5,6,8,9,10,12,13,16],492⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid839 : RecordDataValid section14Catalog 8 (⟨127,(0),[4,8,12,16],[10],494⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨494,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],495⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid840 : RecordDataValid section14Catalog 8 (⟨127,(1),[4,8,12,16],[10],495⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨495,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],496⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid841 : RecordDataValid section14Catalog 8 (⟨127,(2),[4,8,12,16],[10],494⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨494,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],495⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid842 : RecordDataValid section14Catalog 8 (⟨127,(3),[4,8,12,16],[10],496⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨496,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],497⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid843 : RecordDataValid section14Catalog 8 (⟨127,(4),[4,8,12,16],[10],497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨497,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid844 : RecordDataValid section14Catalog 8 (⟨127,(5),[4,8,12,16],[10],497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨497,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid845 : RecordDataValid section14Catalog 8 (⟨127,(6),[4,8,12,16],[10],497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨497,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid846 : RecordDataValid section14Catalog 8 (⟨127,(7),[4,8,12,16],[10],497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨497,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid847 : RecordDataValid section14Catalog 8 (⟨127,(8),[4,8,12,16],[10],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid848 : RecordDataValid section14Catalog 8 (⟨127,(9),[4,8,12,16],[10],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid849 : RecordDataValid section14Catalog 8 (⟨127,(10),[4,8,12,16],[10],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid850 : RecordDataValid section14Catalog 8 (⟨127,(11),[4,8,12,16],[10],498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid851 : RecordDataValid section14Catalog 8 (⟨127,(12),[4,8,12,16],[10],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid852 : RecordDataValid section14Catalog 8 (⟨127,(13),[4,8,12,16],[10],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid853 : RecordDataValid section14Catalog 8 (⟨127,(14),[4,8,12,16],[10],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid854 : RecordDataValid section14Catalog 8 (⟨127,(15),[4,8,12,16],[10],499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid855 : RecordDataValid section14Catalog 8 (⟨129,(0),[4,8,12],[10],500⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨500,[1,4,5,6,8,9,10,12],501⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid856 : RecordDataValid section14Catalog 8 (⟨129,(1),[4,8,12],[10],501⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨501,[1,4,5,6,8,9,10,12],502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid857 : RecordDataValid section14Catalog 8 (⟨129,(2),[4,8,12],[10],502⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨502,[1,4,5,6,8,9,10,12],503⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid858 : RecordDataValid section14Catalog 8 (⟨129,(3),[4,8,12],[10],503⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨503,[1,4,5,6,8,9,10,12],504⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid859 : RecordDataValid section14Catalog 8 (⟨129,(4),[4,8,12],[10],500⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨500,[1,4,5,6,8,9,10,12],501⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid860 : RecordDataValid section14Catalog 8 (⟨129,(5),[4,8,12],[10],501⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨501,[1,4,5,6,8,9,10,12],502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid861 : RecordDataValid section14Catalog 8 (⟨129,(6),[4,8,12],[10],504⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨504,[1,4,5,6,8,9,10,12],505⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid862 : RecordDataValid section14Catalog 8 (⟨129,(7),[4,8,12],[10],503⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨503,[1,4,5,6,8,9,10,12],504⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid863 : RecordDataValid section14Catalog 8 (⟨129,(8),[4,8,12],[10],500⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨500,[1,4,5,6,8,9,10,12],501⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 832).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 832).take 32 = [⟨124,(9),[4,8,12,16],[10],489⟩,⟨124,(10),[4,8,12,16],[10],490⟩,⟨124,(11),[4,8,12,16],[10],491⟩,⟨124,(12),[4,8,12,16],[10],488⟩,⟨124,(13),[4,8,12,16],[10],489⟩,⟨124,(14),[4,8,12,16],[10],493⟩,⟨124,(15),[4,8,12,16],[10],491⟩,⟨127,(0),[4,8,12,16],[10],494⟩,⟨127,(1),[4,8,12,16],[10],495⟩,⟨127,(2),[4,8,12,16],[10],494⟩,⟨127,(3),[4,8,12,16],[10],496⟩,⟨127,(4),[4,8,12,16],[10],497⟩,⟨127,(5),[4,8,12,16],[10],497⟩,⟨127,(6),[4,8,12,16],[10],497⟩,⟨127,(7),[4,8,12,16],[10],497⟩,⟨127,(8),[4,8,12,16],[10],498⟩,⟨127,(9),[4,8,12,16],[10],498⟩,⟨127,(10),[4,8,12,16],[10],498⟩,⟨127,(11),[4,8,12,16],[10],498⟩,⟨127,(12),[4,8,12,16],[10],499⟩,⟨127,(13),[4,8,12,16],[10],499⟩,⟨127,(14),[4,8,12,16],[10],499⟩,⟨127,(15),[4,8,12,16],[10],499⟩,⟨129,(0),[4,8,12],[10],500⟩,⟨129,(1),[4,8,12],[10],501⟩,⟨129,(2),[4,8,12],[10],502⟩,⟨129,(3),[4,8,12],[10],503⟩,⟨129,(4),[4,8,12],[10],500⟩,⟨129,(5),[4,8,12],[10],501⟩,⟨129,(6),[4,8,12],[10],504⟩,⟨129,(7),[4,8,12],[10],503⟩,⟨129,(8),[4,8,12],[10],500⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid832
  · exact recordValid_of_data section14Catalog 8 _ hnum valid833
  · exact recordValid_of_data section14Catalog 8 _ hnum valid834
  · exact recordValid_of_data section14Catalog 8 _ hnum valid835
  · exact recordValid_of_data section14Catalog 8 _ hnum valid836
  · exact recordValid_of_data section14Catalog 8 _ hnum valid837
  · exact recordValid_of_data section14Catalog 8 _ hnum valid838
  · exact recordValid_of_data section14Catalog 8 _ hnum valid839
  · exact recordValid_of_data section14Catalog 8 _ hnum valid840
  · exact recordValid_of_data section14Catalog 8 _ hnum valid841
  · exact recordValid_of_data section14Catalog 8 _ hnum valid842
  · exact recordValid_of_data section14Catalog 8 _ hnum valid843
  · exact recordValid_of_data section14Catalog 8 _ hnum valid844
  · exact recordValid_of_data section14Catalog 8 _ hnum valid845
  · exact recordValid_of_data section14Catalog 8 _ hnum valid846
  · exact recordValid_of_data section14Catalog 8 _ hnum valid847
  · exact recordValid_of_data section14Catalog 8 _ hnum valid848
  · exact recordValid_of_data section14Catalog 8 _ hnum valid849
  · exact recordValid_of_data section14Catalog 8 _ hnum valid850
  · exact recordValid_of_data section14Catalog 8 _ hnum valid851
  · exact recordValid_of_data section14Catalog 8 _ hnum valid852
  · exact recordValid_of_data section14Catalog 8 _ hnum valid853
  · exact recordValid_of_data section14Catalog 8 _ hnum valid854
  · exact recordValid_of_data section14Catalog 8 _ hnum valid855
  · exact recordValid_of_data section14Catalog 8 _ hnum valid856
  · exact recordValid_of_data section14Catalog 8 _ hnum valid857
  · exact recordValid_of_data section14Catalog 8 _ hnum valid858
  · exact recordValid_of_data section14Catalog 8 _ hnum valid859
  · exact recordValid_of_data section14Catalog 8 _ hnum valid860
  · exact recordValid_of_data section14Catalog 8 _ hnum valid861
  · exact recordValid_of_data section14Catalog 8 _ hnum valid862
  · exact recordValid_of_data section14Catalog 8 _ hnum valid863
end Section14Records_8_832_864

#print axioms solution
