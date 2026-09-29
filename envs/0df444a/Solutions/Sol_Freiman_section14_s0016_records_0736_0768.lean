-- Prove2me | solution 1 for Freiman.section14_s0016_records_0736_0768
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T23:03:26.133978+00:00
-- url     : https://prove2.me/submissions/93a3e3ba-7e49-4e6d-b975-d030a6831503

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
namespace Section14Records_16_736_768
private theorem valid736 : RecordDataValid section14Catalog 16 (⟨136,(5),[4,8,12,16],[10],523⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨523,[1,4,5,6,8,9,10,12,13,16],524⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid737 : RecordDataValid section14Catalog 16 (⟨136,(6),[4,8,12,16],[10],527⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨527,[1,4,5,6,8,9,10,12,13,16],528⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid738 : RecordDataValid section14Catalog 16 (⟨136,(7),[4,8,12,16],[10],527⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨527,[1,4,5,6,8,9,10,12,13,16],528⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid739 : RecordDataValid section14Catalog 16 (⟨136,(8),[4,8,12,16],[10],527⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨527,[1,4,5,6,8,9,10,12,13,16],528⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid740 : RecordDataValid section14Catalog 16 (⟨136,(9),[4,8,12,16],[10],528⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨528,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],529⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid741 : RecordDataValid section14Catalog 16 (⟨136,(10),[4,8,12,16],[10],523⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨523,[1,4,5,6,8,9,10,12,13,16],524⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid742 : RecordDataValid section14Catalog 16 (⟨136,(11),[4,8,12,16],[10],526⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨526,[1,4,5,6,8,9,10,12,13,16],527⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid743 : RecordDataValid section14Catalog 16 (⟨136,(12),[4,8,12,16],[10],529⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨529,[1,4,5,6,8,9,10,12,13,16],530⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid744 : RecordDataValid section14Catalog 16 (⟨136,(13),[4,8,12,16],[10],530⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨530,[1,4,5,6,8,9,10,12,13,16],531⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid745 : RecordDataValid section14Catalog 16 (⟨136,(14),[4,8,12,16],[10],531⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨531,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],532⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid746 : RecordDataValid section14Catalog 16 (⟨136,(15),[4,8,12,16],[10],523⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨523,[1,4,5,6,8,9,10,12,13,16],524⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid747 : RecordDataValid section14Catalog 16 (⟨136,(16),[4,8,12,16],[10],526⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨526,[1,4,5,6,8,9,10,12,13,16],527⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid748 : RecordDataValid section14Catalog 16 (⟨136,(17),[4,8,12,16],[10],532⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨532,[1,4,5,6,8,9,10,12,13,16],533⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid749 : RecordDataValid section14Catalog 16 (⟨136,(18),[4,8,12,16],[10],533⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨533,[1,4,5,6,8,9,10,12,13,16],534⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid750 : RecordDataValid section14Catalog 16 (⟨136,(19),[4,8,12,16],[10],534⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨534,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],535⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid751 : RecordDataValid section14Catalog 16 (⟨136,(20),[4,8,12,16],[10],535⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨535,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],536⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid752 : RecordDataValid section14Catalog 16 (⟨136,(21),[4,8,12,16],[10],536⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨536,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],537⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid753 : RecordDataValid section14Catalog 16 (⟨136,(22),[4,8,12,16],[10],537⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨537,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid754 : RecordDataValid section14Catalog 16 (⟨136,(23),[4,8,12,16],[10],538⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨538,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],539⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid755 : RecordDataValid section14Catalog 16 (⟨136,(24),[4,16],[10],537⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨537,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid756 : RecordDataValid section14Catalog 16 (⟨138,(0),[4,8,12,16],[10],539⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨539,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],540⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid757 : RecordDataValid section14Catalog 16 (⟨138,(1),[4,8,12,16],[10],539⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨539,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],540⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid758 : RecordDataValid section14Catalog 16 (⟨138,(2),[4,8,12,16],[10],540⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨540,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],541⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid759 : RecordDataValid section14Catalog 16 (⟨138,(3),[4,8,12,16],[10],541⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨541,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],542⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid760 : RecordDataValid section14Catalog 16 (⟨138,(4),[4,8,12,16],[10],542⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨542,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],543⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid761 : RecordDataValid section14Catalog 16 (⟨138,(5),[4,16],[10],543⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨543,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],544⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid762 : RecordDataValid section14Catalog 16 (⟨138,(6),[4,16],[10],543⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨543,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],544⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid763 : RecordDataValid section14Catalog 16 (⟨138,(7),[4,16],[10],544⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨544,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],545⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid764 : RecordDataValid section14Catalog 16 (⟨138,(8),[4,16],[10],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid765 : RecordDataValid section14Catalog 16 (⟨138,(9),[4,16],[10],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid766 : RecordDataValid section14Catalog 16 (⟨138,(10),[4,8,12,16],[10],545⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨545,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],546⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid767 : RecordDataValid section14Catalog 16 (⟨138,(11),[4,8,12,16],[10],545⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨545,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],546⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 736).take 32, section14RecordValid section14Catalog 16 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 736).take 32 = [⟨136,(5),[4,8,12,16],[10],523⟩,⟨136,(6),[4,8,12,16],[10],527⟩,⟨136,(7),[4,8,12,16],[10],527⟩,⟨136,(8),[4,8,12,16],[10],527⟩,⟨136,(9),[4,8,12,16],[10],528⟩,⟨136,(10),[4,8,12,16],[10],523⟩,⟨136,(11),[4,8,12,16],[10],526⟩,⟨136,(12),[4,8,12,16],[10],529⟩,⟨136,(13),[4,8,12,16],[10],530⟩,⟨136,(14),[4,8,12,16],[10],531⟩,⟨136,(15),[4,8,12,16],[10],523⟩,⟨136,(16),[4,8,12,16],[10],526⟩,⟨136,(17),[4,8,12,16],[10],532⟩,⟨136,(18),[4,8,12,16],[10],533⟩,⟨136,(19),[4,8,12,16],[10],534⟩,⟨136,(20),[4,8,12,16],[10],535⟩,⟨136,(21),[4,8,12,16],[10],536⟩,⟨136,(22),[4,8,12,16],[10],537⟩,⟨136,(23),[4,8,12,16],[10],538⟩,⟨136,(24),[4,16],[10],537⟩,⟨138,(0),[4,8,12,16],[10],539⟩,⟨138,(1),[4,8,12,16],[10],539⟩,⟨138,(2),[4,8,12,16],[10],540⟩,⟨138,(3),[4,8,12,16],[10],541⟩,⟨138,(4),[4,8,12,16],[10],542⟩,⟨138,(5),[4,16],[10],543⟩,⟨138,(6),[4,16],[10],543⟩,⟨138,(7),[4,16],[10],544⟩,⟨138,(8),[4,16],[10],517⟩,⟨138,(9),[4,16],[10],518⟩,⟨138,(10),[4,8,12,16],[10],545⟩,⟨138,(11),[4,8,12,16],[10],545⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 16 _ hnum valid736
  · exact recordValid_of_data section14Catalog 16 _ hnum valid737
  · exact recordValid_of_data section14Catalog 16 _ hnum valid738
  · exact recordValid_of_data section14Catalog 16 _ hnum valid739
  · exact recordValid_of_data section14Catalog 16 _ hnum valid740
  · exact recordValid_of_data section14Catalog 16 _ hnum valid741
  · exact recordValid_of_data section14Catalog 16 _ hnum valid742
  · exact recordValid_of_data section14Catalog 16 _ hnum valid743
  · exact recordValid_of_data section14Catalog 16 _ hnum valid744
  · exact recordValid_of_data section14Catalog 16 _ hnum valid745
  · exact recordValid_of_data section14Catalog 16 _ hnum valid746
  · exact recordValid_of_data section14Catalog 16 _ hnum valid747
  · exact recordValid_of_data section14Catalog 16 _ hnum valid748
  · exact recordValid_of_data section14Catalog 16 _ hnum valid749
  · exact recordValid_of_data section14Catalog 16 _ hnum valid750
  · exact recordValid_of_data section14Catalog 16 _ hnum valid751
  · exact recordValid_of_data section14Catalog 16 _ hnum valid752
  · exact recordValid_of_data section14Catalog 16 _ hnum valid753
  · exact recordValid_of_data section14Catalog 16 _ hnum valid754
  · exact recordValid_of_data section14Catalog 16 _ hnum valid755
  · exact recordValid_of_data section14Catalog 16 _ hnum valid756
  · exact recordValid_of_data section14Catalog 16 _ hnum valid757
  · exact recordValid_of_data section14Catalog 16 _ hnum valid758
  · exact recordValid_of_data section14Catalog 16 _ hnum valid759
  · exact recordValid_of_data section14Catalog 16 _ hnum valid760
  · exact recordValid_of_data section14Catalog 16 _ hnum valid761
  · exact recordValid_of_data section14Catalog 16 _ hnum valid762
  · exact recordValid_of_data section14Catalog 16 _ hnum valid763
  · exact recordValid_of_data section14Catalog 16 _ hnum valid764
  · exact recordValid_of_data section14Catalog 16 _ hnum valid765
  · exact recordValid_of_data section14Catalog 16 _ hnum valid766
  · exact recordValid_of_data section14Catalog 16 _ hnum valid767
end Section14Records_16_736_768

#print axioms solution
