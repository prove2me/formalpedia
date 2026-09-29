-- Prove2me | solution 1 for Freiman.section14_s0015_records_0832_0864
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T19:06:21.667955+00:00
-- url     : https://prove2.me/submissions/4802c4d3-7007-4490-9465-80dc58dd86c6

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
namespace Section14Records_15_832_864
private theorem valid832 : RecordDataValid section14Catalog 15 (⟨221,(11),[3,7,15],[10],519⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨519,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],520⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid833 : RecordDataValid section14Catalog 15 (⟨221,(12),[3,7,15],[10],520⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨520,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],521⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid834 : RecordDataValid section14Catalog 15 (⟨221,(13),[3,7,15],[10],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid835 : RecordDataValid section14Catalog 15 (⟨221,(14),[3,7,15],[10],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid836 : RecordDataValid section14Catalog 15 (⟨221,(15),[3,7,15],[10],521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨521,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],522⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid837 : RecordDataValid section14Catalog 15 (⟨221,(16),[3,7,15],[10],521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨521,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],522⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid838 : RecordDataValid section14Catalog 15 (⟨221,(17),[3,7,15],[10],521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨521,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],522⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid839 : RecordDataValid section14Catalog 15 (⟨221,(18),[3,7,15],[10],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid840 : RecordDataValid section14Catalog 15 (⟨221,(19),[3,7,15],[10],521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨521,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],522⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid841 : RecordDataValid section14Catalog 15 (⟨221,(20),[3,7,15],[10],522⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨522,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],523⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid842 : RecordDataValid section14Catalog 15 (⟨221,(21),[3,7,15],[10],522⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨522,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],523⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid843 : RecordDataValid section14Catalog 15 (⟨221,(22),[3,7,15],[10],522⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨522,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],523⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid844 : RecordDataValid section14Catalog 15 (⟨221,(23),[3,7,15],[10],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid845 : RecordDataValid section14Catalog 15 (⟨221,(24),[3,7,15],[10],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid846 : RecordDataValid section14Catalog 15 (⟨222,(0),[3,15],[10],735⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨735,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],736⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid847 : RecordDataValid section14Catalog 15 (⟨222,(1),[3,4,8,12,15,16],[10],736⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨736,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],737⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid848 : RecordDataValid section14Catalog 15 (⟨222,(2),[3,4,7,15,16],[10],737⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨737,[1,2,3,4,5,6,7,10,11,13,14,15,16],738⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid849 : RecordDataValid section14Catalog 15 (⟨222,(3),[3,4,8,12,15,16],[10],736⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨736,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],737⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid850 : RecordDataValid section14Catalog 15 (⟨222,(4),[3,4,7,8,12,15,16],[10],525⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨525,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],526⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid851 : RecordDataValid section14Catalog 15 (⟨222,(5),[3,4,8,12,15,16],[10],735⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨735,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],736⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid852 : RecordDataValid section14Catalog 15 (⟨222,(6),[3,15],[10],738⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨738,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],739⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid853 : RecordDataValid section14Catalog 15 (⟨222,(7),[3,4,7,15,16],[10],739⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨739,[1,2,3,4,5,6,7,10,11,13,14,15,16],740⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid854 : RecordDataValid section14Catalog 15 (⟨222,(8),[3,4,8,12,15,16],[10],740⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨740,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],741⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid855 : RecordDataValid section14Catalog 15 (⟨222,(9),[3,4,7,8,12,15,16],[10],528⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨528,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],529⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid856 : RecordDataValid section14Catalog 15 (⟨222,(10),[3,7,15],[10],741⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨741,[1,2,3,6,7,10,11,13,14,15],742⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid857 : RecordDataValid section14Catalog 15 (⟨222,(11),[3,7,15],[10],742⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨742,[1,2,3,6,7,10,11,13,14,15],743⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid858 : RecordDataValid section14Catalog 15 (⟨222,(12),[3,7,15],[10],743⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨743,[1,2,3,6,7,11,13,14,15],744⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid859 : RecordDataValid section14Catalog 15 (⟨222,(13),[3,7,15],[10],744⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨744,[1,2,3,6,7,10,11,13,14,15],745⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid860 : RecordDataValid section14Catalog 15 (⟨222,(14),[3,4,7,8,12,15,16],[10],531⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨531,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],532⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid861 : RecordDataValid section14Catalog 15 (⟨222,(15),[3,4,8,12,15,16],[10],735⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨735,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],736⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid862 : RecordDataValid section14Catalog 15 (⟨222,(16),[3,4,8,12,15,16],[10],738⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨738,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],739⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid863 : RecordDataValid section14Catalog 15 (⟨222,(17),[3,4,7,15,16],[10],745⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨745,[1,2,3,4,5,6,7,10,11,13,14,15,16],746⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 832).take 32, section14RecordValid section14Catalog 15 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 832).take 32 = [⟨221,(11),[3,7,15],[10],519⟩,⟨221,(12),[3,7,15],[10],520⟩,⟨221,(13),[3,7,15],[10],517⟩,⟨221,(14),[3,7,15],[10],518⟩,⟨221,(15),[3,7,15],[10],521⟩,⟨221,(16),[3,7,15],[10],521⟩,⟨221,(17),[3,7,15],[10],521⟩,⟨221,(18),[3,7,15],[10],517⟩,⟨221,(19),[3,7,15],[10],521⟩,⟨221,(20),[3,7,15],[10],522⟩,⟨221,(21),[3,7,15],[10],522⟩,⟨221,(22),[3,7,15],[10],522⟩,⟨221,(23),[3,7,15],[10],517⟩,⟨221,(24),[3,7,15],[10],518⟩,⟨222,(0),[3,15],[10],735⟩,⟨222,(1),[3,4,8,12,15,16],[10],736⟩,⟨222,(2),[3,4,7,15,16],[10],737⟩,⟨222,(3),[3,4,8,12,15,16],[10],736⟩,⟨222,(4),[3,4,7,8,12,15,16],[10],525⟩,⟨222,(5),[3,4,8,12,15,16],[10],735⟩,⟨222,(6),[3,15],[10],738⟩,⟨222,(7),[3,4,7,15,16],[10],739⟩,⟨222,(8),[3,4,8,12,15,16],[10],740⟩,⟨222,(9),[3,4,7,8,12,15,16],[10],528⟩,⟨222,(10),[3,7,15],[10],741⟩,⟨222,(11),[3,7,15],[10],742⟩,⟨222,(12),[3,7,15],[10],743⟩,⟨222,(13),[3,7,15],[10],744⟩,⟨222,(14),[3,4,7,8,12,15,16],[10],531⟩,⟨222,(15),[3,4,8,12,15,16],[10],735⟩,⟨222,(16),[3,4,8,12,15,16],[10],738⟩,⟨222,(17),[3,4,7,15,16],[10],745⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 15 _ hnum valid832
  · exact recordValid_of_data section14Catalog 15 _ hnum valid833
  · exact recordValid_of_data section14Catalog 15 _ hnum valid834
  · exact recordValid_of_data section14Catalog 15 _ hnum valid835
  · exact recordValid_of_data section14Catalog 15 _ hnum valid836
  · exact recordValid_of_data section14Catalog 15 _ hnum valid837
  · exact recordValid_of_data section14Catalog 15 _ hnum valid838
  · exact recordValid_of_data section14Catalog 15 _ hnum valid839
  · exact recordValid_of_data section14Catalog 15 _ hnum valid840
  · exact recordValid_of_data section14Catalog 15 _ hnum valid841
  · exact recordValid_of_data section14Catalog 15 _ hnum valid842
  · exact recordValid_of_data section14Catalog 15 _ hnum valid843
  · exact recordValid_of_data section14Catalog 15 _ hnum valid844
  · exact recordValid_of_data section14Catalog 15 _ hnum valid845
  · exact recordValid_of_data section14Catalog 15 _ hnum valid846
  · exact recordValid_of_data section14Catalog 15 _ hnum valid847
  · exact recordValid_of_data section14Catalog 15 _ hnum valid848
  · exact recordValid_of_data section14Catalog 15 _ hnum valid849
  · exact recordValid_of_data section14Catalog 15 _ hnum valid850
  · exact recordValid_of_data section14Catalog 15 _ hnum valid851
  · exact recordValid_of_data section14Catalog 15 _ hnum valid852
  · exact recordValid_of_data section14Catalog 15 _ hnum valid853
  · exact recordValid_of_data section14Catalog 15 _ hnum valid854
  · exact recordValid_of_data section14Catalog 15 _ hnum valid855
  · exact recordValid_of_data section14Catalog 15 _ hnum valid856
  · exact recordValid_of_data section14Catalog 15 _ hnum valid857
  · exact recordValid_of_data section14Catalog 15 _ hnum valid858
  · exact recordValid_of_data section14Catalog 15 _ hnum valid859
  · exact recordValid_of_data section14Catalog 15 _ hnum valid860
  · exact recordValid_of_data section14Catalog 15 _ hnum valid861
  · exact recordValid_of_data section14Catalog 15 _ hnum valid862
  · exact recordValid_of_data section14Catalog 15 _ hnum valid863
end Section14Records_15_832_864

#print axioms solution
