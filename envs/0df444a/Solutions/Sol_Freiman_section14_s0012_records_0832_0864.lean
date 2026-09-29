-- Prove2me | solution 1 for Freiman.section14_s0012_records_0832_0864
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T04:37:44.583989+00:00
-- url     : https://prove2.me/submissions/bfe810b9-d7bd-4bc9-85f4-6cc02d7c56e6

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
namespace Section14Records_12_832_864
private theorem valid832 : RecordDataValid section14Catalog 12 (⟨136,(14),[4,8,12,16],[10],531⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨531,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],532⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid833 : RecordDataValid section14Catalog 12 (⟨136,(15),[4,8,12,16],[10],523⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨523,[1,4,5,6,8,9,10,12,13,16],524⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid834 : RecordDataValid section14Catalog 12 (⟨136,(16),[4,8,12,16],[10],526⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨526,[1,4,5,6,8,9,10,12,13,16],527⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid835 : RecordDataValid section14Catalog 12 (⟨136,(17),[4,8,12,16],[10],532⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨532,[1,4,5,6,8,9,10,12,13,16],533⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid836 : RecordDataValid section14Catalog 12 (⟨136,(18),[4,8,12,16],[10],533⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨533,[1,4,5,6,8,9,10,12,13,16],534⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid837 : RecordDataValid section14Catalog 12 (⟨136,(19),[4,8,12,16],[10],534⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨534,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],535⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid838 : RecordDataValid section14Catalog 12 (⟨136,(20),[4,8,12,16],[10],535⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨535,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],536⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid839 : RecordDataValid section14Catalog 12 (⟨136,(21),[4,8,12,16],[10],536⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨536,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],537⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid840 : RecordDataValid section14Catalog 12 (⟨136,(22),[4,8,12,16],[10],537⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨537,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid841 : RecordDataValid section14Catalog 12 (⟨136,(23),[4,8,12,16],[10],538⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨538,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],539⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid842 : RecordDataValid section14Catalog 12 (⟨136,(24),[8,12],[10],531⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨531,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],532⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid843 : RecordDataValid section14Catalog 12 (⟨138,(0),[4,8,12,16],[10],539⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨539,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],540⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid844 : RecordDataValid section14Catalog 12 (⟨138,(1),[4,8,12,16],[10],539⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨539,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],540⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid845 : RecordDataValid section14Catalog 12 (⟨138,(2),[4,8,12,16],[10],540⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨540,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],541⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid846 : RecordDataValid section14Catalog 12 (⟨138,(3),[4,8,12,16],[10],541⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨541,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],542⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid847 : RecordDataValid section14Catalog 12 (⟨138,(4),[4,8,12,16],[10],542⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨542,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],543⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid848 : RecordDataValid section14Catalog 12 (⟨138,(5),[8,12],[10],1635⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1635,[8,12],1640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid849 : RecordDataValid section14Catalog 12 (⟨138,(6),[8,12],[10],1635⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1635,[8,12],1640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid850 : RecordDataValid section14Catalog 12 (⟨138,(7),[8,12],[10],1636⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1636,[8,12],1641⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid851 : RecordDataValid section14Catalog 12 (⟨138,(8),[8,12],[10],1637⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1637,[8,12],1642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid852 : RecordDataValid section14Catalog 12 (⟨138,(9),[8,12],[10],1638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1638,[8,12],1643⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid853 : RecordDataValid section14Catalog 12 (⟨138,(10),[4,8,12,16],[10],545⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨545,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],546⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid854 : RecordDataValid section14Catalog 12 (⟨138,(11),[4,8,12,16],[10],545⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨545,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],546⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid855 : RecordDataValid section14Catalog 12 (⟨138,(12),[4,8,12,16],[10],544⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨544,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],545⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid856 : RecordDataValid section14Catalog 12 (⟨138,(13),[4,8,12,16],[10],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid857 : RecordDataValid section14Catalog 12 (⟨138,(14),[4,8,12,16],[10],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid858 : RecordDataValid section14Catalog 12 (⟨138,(15),[4,8,12,16],[10],546⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨546,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],547⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid859 : RecordDataValid section14Catalog 12 (⟨138,(16),[4,8,12,16],[10],546⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨546,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],547⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid860 : RecordDataValid section14Catalog 12 (⟨138,(17),[4,8,12,16],[10],544⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨544,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],545⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid861 : RecordDataValid section14Catalog 12 (⟨138,(18),[4,8,12,16],[10],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid862 : RecordDataValid section14Catalog 12 (⟨138,(19),[4,8,12,16],[10],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid863 : RecordDataValid section14Catalog 12 (⟨138,(20),[4,8,12,16],[10],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 832).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 832).take 32 = [⟨136,(14),[4,8,12,16],[10],531⟩,⟨136,(15),[4,8,12,16],[10],523⟩,⟨136,(16),[4,8,12,16],[10],526⟩,⟨136,(17),[4,8,12,16],[10],532⟩,⟨136,(18),[4,8,12,16],[10],533⟩,⟨136,(19),[4,8,12,16],[10],534⟩,⟨136,(20),[4,8,12,16],[10],535⟩,⟨136,(21),[4,8,12,16],[10],536⟩,⟨136,(22),[4,8,12,16],[10],537⟩,⟨136,(23),[4,8,12,16],[10],538⟩,⟨136,(24),[8,12],[10],531⟩,⟨138,(0),[4,8,12,16],[10],539⟩,⟨138,(1),[4,8,12,16],[10],539⟩,⟨138,(2),[4,8,12,16],[10],540⟩,⟨138,(3),[4,8,12,16],[10],541⟩,⟨138,(4),[4,8,12,16],[10],542⟩,⟨138,(5),[8,12],[10],1635⟩,⟨138,(6),[8,12],[10],1635⟩,⟨138,(7),[8,12],[10],1636⟩,⟨138,(8),[8,12],[10],1637⟩,⟨138,(9),[8,12],[10],1638⟩,⟨138,(10),[4,8,12,16],[10],545⟩,⟨138,(11),[4,8,12,16],[10],545⟩,⟨138,(12),[4,8,12,16],[10],544⟩,⟨138,(13),[4,8,12,16],[10],517⟩,⟨138,(14),[4,8,12,16],[10],518⟩,⟨138,(15),[4,8,12,16],[10],546⟩,⟨138,(16),[4,8,12,16],[10],546⟩,⟨138,(17),[4,8,12,16],[10],544⟩,⟨138,(18),[4,8,12,16],[10],517⟩,⟨138,(19),[4,8,12,16],[10],518⟩,⟨138,(20),[4,8,12,16],[10],547⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid832
  · exact recordValid_of_data section14Catalog 12 _ hnum valid833
  · exact recordValid_of_data section14Catalog 12 _ hnum valid834
  · exact recordValid_of_data section14Catalog 12 _ hnum valid835
  · exact recordValid_of_data section14Catalog 12 _ hnum valid836
  · exact recordValid_of_data section14Catalog 12 _ hnum valid837
  · exact recordValid_of_data section14Catalog 12 _ hnum valid838
  · exact recordValid_of_data section14Catalog 12 _ hnum valid839
  · exact recordValid_of_data section14Catalog 12 _ hnum valid840
  · exact recordValid_of_data section14Catalog 12 _ hnum valid841
  · exact recordValid_of_data section14Catalog 12 _ hnum valid842
  · exact recordValid_of_data section14Catalog 12 _ hnum valid843
  · exact recordValid_of_data section14Catalog 12 _ hnum valid844
  · exact recordValid_of_data section14Catalog 12 _ hnum valid845
  · exact recordValid_of_data section14Catalog 12 _ hnum valid846
  · exact recordValid_of_data section14Catalog 12 _ hnum valid847
  · exact recordValid_of_data section14Catalog 12 _ hnum valid848
  · exact recordValid_of_data section14Catalog 12 _ hnum valid849
  · exact recordValid_of_data section14Catalog 12 _ hnum valid850
  · exact recordValid_of_data section14Catalog 12 _ hnum valid851
  · exact recordValid_of_data section14Catalog 12 _ hnum valid852
  · exact recordValid_of_data section14Catalog 12 _ hnum valid853
  · exact recordValid_of_data section14Catalog 12 _ hnum valid854
  · exact recordValid_of_data section14Catalog 12 _ hnum valid855
  · exact recordValid_of_data section14Catalog 12 _ hnum valid856
  · exact recordValid_of_data section14Catalog 12 _ hnum valid857
  · exact recordValid_of_data section14Catalog 12 _ hnum valid858
  · exact recordValid_of_data section14Catalog 12 _ hnum valid859
  · exact recordValid_of_data section14Catalog 12 _ hnum valid860
  · exact recordValid_of_data section14Catalog 12 _ hnum valid861
  · exact recordValid_of_data section14Catalog 12 _ hnum valid862
  · exact recordValid_of_data section14Catalog 12 _ hnum valid863
end Section14Records_12_832_864

#print axioms solution
