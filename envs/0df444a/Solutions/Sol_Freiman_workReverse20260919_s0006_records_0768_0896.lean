-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_0768_0896
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:47:54.993739+00:00
-- url     : https://prove2.me/submissions/8b094517-3762-4a0a-b4b8-ccc3104fd71d

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0768_0800
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_768_800
private theorem valid768 : RecordDataValid section14Catalog 6 (⟨40,(7),[6],[150],1533⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1533,[6,7,9,10,11],1538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid769 : RecordDataValid section14Catalog 6 (⟨40,(8),[1,2,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid770 : RecordDataValid section14Catalog 6 (⟨40,(8),[6],[150],1533⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1533,[6,7,9,10,11],1538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid771 : RecordDataValid section14Catalog 6 (⟨40,(9),[1,2,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid772 : RecordDataValid section14Catalog 6 (⟨40,(9),[6],[150],1533⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1533,[6,7,9,10,11],1538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid773 : RecordDataValid section14Catalog 6 (⟨40,(10),[1,2,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid774 : RecordDataValid section14Catalog 6 (⟨40,(10),[6],[150],1534⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1534,[6,7,9,10,11,12],1539⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid775 : RecordDataValid section14Catalog 6 (⟨40,(11),[1,2,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid776 : RecordDataValid section14Catalog 6 (⟨40,(11),[6],[150],1535⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1535,[6,9,10],1540⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid777 : RecordDataValid section14Catalog 6 (⟨40,(12),[1,2,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid778 : RecordDataValid section14Catalog 6 (⟨40,(12),[6],[150],1536⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1536,[6,7,9,10,11],1541⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid779 : RecordDataValid section14Catalog 6 (⟨40,(13),[1,2,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid780 : RecordDataValid section14Catalog 6 (⟨40,(13),[6],[150],1535⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1535,[6,9,10],1540⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid781 : RecordDataValid section14Catalog 6 (⟨40,(14),[1,2,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid782 : RecordDataValid section14Catalog 6 (⟨40,(14),[6],[150],1537⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1537,[6,9,10],1542⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid783 : RecordDataValid section14Catalog 6 (⟨40,(15),[1,2,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid784 : RecordDataValid section14Catalog 6 (⟨40,(15),[6],[150],1534⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1534,[6,7,9,10,11,12],1539⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid785 : RecordDataValid section14Catalog 6 (⟨40,(16),[1,2,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid786 : RecordDataValid section14Catalog 6 (⟨40,(16),[6],[150],1538⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1538,[6,7,9,10,11],1543⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid787 : RecordDataValid section14Catalog 6 (⟨40,(17),[1,2,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid788 : RecordDataValid section14Catalog 6 (⟨40,(17),[6],[150],1538⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1538,[6,7,9,10,11],1543⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid789 : RecordDataValid section14Catalog 6 (⟨40,(18),[1,2,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid790 : RecordDataValid section14Catalog 6 (⟨40,(18),[6],[150],1538⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1538,[6,7,9,10,11],1543⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid791 : RecordDataValid section14Catalog 6 (⟨40,(19),[1,2,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid792 : RecordDataValid section14Catalog 6 (⟨40,(19),[6],[150],1538⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1538,[6,7,9,10,11],1543⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid793 : RecordDataValid section14Catalog 6 (⟨40,(20),[1,2,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid794 : RecordDataValid section14Catalog 6 (⟨40,(20),[6],[150],1534⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1534,[6,7,9,10,11,12],1539⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid795 : RecordDataValid section14Catalog 6 (⟨40,(21),[1,2,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid796 : RecordDataValid section14Catalog 6 (⟨40,(21),[6],[150],1535⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1535,[6,9,10],1540⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid797 : RecordDataValid section14Catalog 6 (⟨40,(22),[1,2,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid798 : RecordDataValid section14Catalog 6 (⟨40,(22),[6],[150],1536⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1536,[6,7,9,10,11],1541⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid799 : RecordDataValid section14Catalog 6 (⟨40,(23),[1,2,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_0768_0800 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 768).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 768).take 32 = [⟨40,(7),[6],[150],1533⟩,⟨40,(8),[1,2,5,6,13,14],[170,174,190],3⟩,⟨40,(8),[6],[150],1533⟩,⟨40,(9),[1,2,5,6,13,14],[170,174,190],3⟩,⟨40,(9),[6],[150],1533⟩,⟨40,(10),[1,2,5,6,13,14],[170,174,190],3⟩,⟨40,(10),[6],[150],1534⟩,⟨40,(11),[1,2,5,6,13,14],[170,174,190],3⟩,⟨40,(11),[6],[150],1535⟩,⟨40,(12),[1,2,5,6,13,14],[170,174,190],3⟩,⟨40,(12),[6],[150],1536⟩,⟨40,(13),[1,2,5,6,13,14],[170,174,190],3⟩,⟨40,(13),[6],[150],1535⟩,⟨40,(14),[1,2,5,6,13,14],[170,174,190],3⟩,⟨40,(14),[6],[150],1537⟩,⟨40,(15),[1,2,5,6,13,14],[170,174,190],3⟩,⟨40,(15),[6],[150],1534⟩,⟨40,(16),[1,2,5,6,13,14],[170,174,190],3⟩,⟨40,(16),[6],[150],1538⟩,⟨40,(17),[1,2,5,6,13,14],[170,174,190],3⟩,⟨40,(17),[6],[150],1538⟩,⟨40,(18),[1,2,5,6,13,14],[170,174,190],3⟩,⟨40,(18),[6],[150],1538⟩,⟨40,(19),[1,2,5,6,13,14],[170,174,190],3⟩,⟨40,(19),[6],[150],1538⟩,⟨40,(20),[1,2,5,6,13,14],[170,174,190],3⟩,⟨40,(20),[6],[150],1534⟩,⟨40,(21),[1,2,5,6,13,14],[170,174,190],3⟩,⟨40,(21),[6],[150],1535⟩,⟨40,(22),[1,2,5,6,13,14],[170,174,190],3⟩,⟨40,(22),[6],[150],1536⟩,⟨40,(23),[1,2,5,6,13,14],[170,174,190],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid768
  · exact recordValid_of_data section14Catalog 6 _ hnum valid769
  · exact recordValid_of_data section14Catalog 6 _ hnum valid770
  · exact recordValid_of_data section14Catalog 6 _ hnum valid771
  · exact recordValid_of_data section14Catalog 6 _ hnum valid772
  · exact recordValid_of_data section14Catalog 6 _ hnum valid773
  · exact recordValid_of_data section14Catalog 6 _ hnum valid774
  · exact recordValid_of_data section14Catalog 6 _ hnum valid775
  · exact recordValid_of_data section14Catalog 6 _ hnum valid776
  · exact recordValid_of_data section14Catalog 6 _ hnum valid777
  · exact recordValid_of_data section14Catalog 6 _ hnum valid778
  · exact recordValid_of_data section14Catalog 6 _ hnum valid779
  · exact recordValid_of_data section14Catalog 6 _ hnum valid780
  · exact recordValid_of_data section14Catalog 6 _ hnum valid781
  · exact recordValid_of_data section14Catalog 6 _ hnum valid782
  · exact recordValid_of_data section14Catalog 6 _ hnum valid783
  · exact recordValid_of_data section14Catalog 6 _ hnum valid784
  · exact recordValid_of_data section14Catalog 6 _ hnum valid785
  · exact recordValid_of_data section14Catalog 6 _ hnum valid786
  · exact recordValid_of_data section14Catalog 6 _ hnum valid787
  · exact recordValid_of_data section14Catalog 6 _ hnum valid788
  · exact recordValid_of_data section14Catalog 6 _ hnum valid789
  · exact recordValid_of_data section14Catalog 6 _ hnum valid790
  · exact recordValid_of_data section14Catalog 6 _ hnum valid791
  · exact recordValid_of_data section14Catalog 6 _ hnum valid792
  · exact recordValid_of_data section14Catalog 6 _ hnum valid793
  · exact recordValid_of_data section14Catalog 6 _ hnum valid794
  · exact recordValid_of_data section14Catalog 6 _ hnum valid795
  · exact recordValid_of_data section14Catalog 6 _ hnum valid796
  · exact recordValid_of_data section14Catalog 6 _ hnum valid797
  · exact recordValid_of_data section14Catalog 6 _ hnum valid798
  · exact recordValid_of_data section14Catalog 6 _ hnum valid799
end Section14Records_6_768_800

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0768_0800


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0800_0832
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_800_832
private theorem valid800 : RecordDataValid section14Catalog 6 (⟨40,(23),[6],[150],1535⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1535,[6,9,10],1540⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid801 : RecordDataValid section14Catalog 6 (⟨40,(24),[1,2,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid802 : RecordDataValid section14Catalog 6 (⟨40,(24),[6],[150],1537⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1537,[6,9,10],1542⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid803 : RecordDataValid section14Catalog 6 (⟨42,(0),[1,2,5,6,13,14],[170],253⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨253,[1,2,3,4,5,6,7,8,13,14,15,16],254⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid804 : RecordDataValid section14Catalog 6 (⟨42,(0),[1,2,5,6,13,14],[174],288⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨288,[1,2,3,5,6,7,13,14,15],289⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid805 : RecordDataValid section14Catalog 6 (⟨42,(0),[1,2,5,6,13,14],[190],312⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨312,[1,2,4,5,6,8,13,14,16],313⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid806 : RecordDataValid section14Catalog 6 (⟨42,(0),[6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid807 : RecordDataValid section14Catalog 6 (⟨42,(1),[1,2,5,6,13,14],[170],254⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨254,[1,2,3,4,5,6,7,8,13,14,15,16],255⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid808 : RecordDataValid section14Catalog 6 (⟨42,(1),[1,2,5,6,13,14],[174],289⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨289,[1,2,3,5,6,7,13,14,15],290⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid809 : RecordDataValid section14Catalog 6 (⟨42,(1),[1,2,5,6,13,14],[190],313⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨313,[1,2,4,5,6,8,13,14,16],314⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid810 : RecordDataValid section14Catalog 6 (⟨42,(1),[6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid811 : RecordDataValid section14Catalog 6 (⟨42,(2),[1,2,5,6,13,14],[170],253⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨253,[1,2,3,4,5,6,7,8,13,14,15,16],254⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid812 : RecordDataValid section14Catalog 6 (⟨42,(2),[1,2,5,6,13,14],[174],288⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨288,[1,2,3,5,6,7,13,14,15],289⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid813 : RecordDataValid section14Catalog 6 (⟨42,(2),[1,2,5,6,13,14],[190],312⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨312,[1,2,4,5,6,8,13,14,16],313⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid814 : RecordDataValid section14Catalog 6 (⟨42,(2),[6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid815 : RecordDataValid section14Catalog 6 (⟨42,(3),[1,2,5,6,13,14],[170],255⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨255,[1,2,3,4,5,6,7,8,13,14,15,16],256⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid816 : RecordDataValid section14Catalog 6 (⟨42,(3),[1,2,5,6,13,14],[174],290⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨290,[1,2,3,5,6,7,13,14,15],291⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid817 : RecordDataValid section14Catalog 6 (⟨42,(3),[1,2,5,6,13,14],[190],314⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨314,[1,2,4,5,6,8,13,14,16],315⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid818 : RecordDataValid section14Catalog 6 (⟨42,(3),[6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid819 : RecordDataValid section14Catalog 6 (⟨42,(4),[1,2,5,6,13,14],[170],256⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨256,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],257⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid820 : RecordDataValid section14Catalog 6 (⟨42,(4),[1,2,5,6,13,14],[174],291⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨291,[1,2,3,5,6,7,13,14,15],292⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid821 : RecordDataValid section14Catalog 6 (⟨42,(4),[1,2,5,6,13,14],[190],315⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨315,[1,2,4,5,6,8,9,10,12,13,14,16],316⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid822 : RecordDataValid section14Catalog 6 (⟨42,(4),[6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid823 : RecordDataValid section14Catalog 6 (⟨42,(5),[1,2,5,6,13,14],[170],253⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨253,[1,2,3,4,5,6,7,8,13,14,15,16],254⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid824 : RecordDataValid section14Catalog 6 (⟨42,(5),[1,2,5,6,13,14],[174],288⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨288,[1,2,3,5,6,7,13,14,15],289⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid825 : RecordDataValid section14Catalog 6 (⟨42,(5),[1,2,5,6,13,14],[190],312⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨312,[1,2,4,5,6,8,13,14,16],313⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid826 : RecordDataValid section14Catalog 6 (⟨42,(5),[6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid827 : RecordDataValid section14Catalog 6 (⟨42,(6),[1,2,5,6,13,14],[170],254⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨254,[1,2,3,4,5,6,7,8,13,14,15,16],255⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid828 : RecordDataValid section14Catalog 6 (⟨42,(6),[1,2,5,6,13,14],[174],289⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨289,[1,2,3,5,6,7,13,14,15],290⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid829 : RecordDataValid section14Catalog 6 (⟨42,(6),[1,2,5,6,13,14],[190],313⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨313,[1,2,4,5,6,8,13,14,16],314⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid830 : RecordDataValid section14Catalog 6 (⟨42,(6),[6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid831 : RecordDataValid section14Catalog 6 (⟨42,(7),[1,2,5,6,13,14],[170],253⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨253,[1,2,3,4,5,6,7,8,13,14,15,16],254⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_0800_0832 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 800).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 800).take 32 = [⟨40,(23),[6],[150],1535⟩,⟨40,(24),[1,2,5,6,13,14],[170,174,190],3⟩,⟨40,(24),[6],[150],1537⟩,⟨42,(0),[1,2,5,6,13,14],[170],253⟩,⟨42,(0),[1,2,5,6,13,14],[174],288⟩,⟨42,(0),[1,2,5,6,13,14],[190],312⟩,⟨42,(0),[6],[150],3⟩,⟨42,(1),[1,2,5,6,13,14],[170],254⟩,⟨42,(1),[1,2,5,6,13,14],[174],289⟩,⟨42,(1),[1,2,5,6,13,14],[190],313⟩,⟨42,(1),[6],[150],3⟩,⟨42,(2),[1,2,5,6,13,14],[170],253⟩,⟨42,(2),[1,2,5,6,13,14],[174],288⟩,⟨42,(2),[1,2,5,6,13,14],[190],312⟩,⟨42,(2),[6],[150],3⟩,⟨42,(3),[1,2,5,6,13,14],[170],255⟩,⟨42,(3),[1,2,5,6,13,14],[174],290⟩,⟨42,(3),[1,2,5,6,13,14],[190],314⟩,⟨42,(3),[6],[150],3⟩,⟨42,(4),[1,2,5,6,13,14],[170],256⟩,⟨42,(4),[1,2,5,6,13,14],[174],291⟩,⟨42,(4),[1,2,5,6,13,14],[190],315⟩,⟨42,(4),[6],[150],3⟩,⟨42,(5),[1,2,5,6,13,14],[170],253⟩,⟨42,(5),[1,2,5,6,13,14],[174],288⟩,⟨42,(5),[1,2,5,6,13,14],[190],312⟩,⟨42,(5),[6],[150],3⟩,⟨42,(6),[1,2,5,6,13,14],[170],254⟩,⟨42,(6),[1,2,5,6,13,14],[174],289⟩,⟨42,(6),[1,2,5,6,13,14],[190],313⟩,⟨42,(6),[6],[150],3⟩,⟨42,(7),[1,2,5,6,13,14],[170],253⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid800
  · exact recordValid_of_data section14Catalog 6 _ hnum valid801
  · exact recordValid_of_data section14Catalog 6 _ hnum valid802
  · exact recordValid_of_data section14Catalog 6 _ hnum valid803
  · exact recordValid_of_data section14Catalog 6 _ hnum valid804
  · exact recordValid_of_data section14Catalog 6 _ hnum valid805
  · exact recordValid_of_data section14Catalog 6 _ hnum valid806
  · exact recordValid_of_data section14Catalog 6 _ hnum valid807
  · exact recordValid_of_data section14Catalog 6 _ hnum valid808
  · exact recordValid_of_data section14Catalog 6 _ hnum valid809
  · exact recordValid_of_data section14Catalog 6 _ hnum valid810
  · exact recordValid_of_data section14Catalog 6 _ hnum valid811
  · exact recordValid_of_data section14Catalog 6 _ hnum valid812
  · exact recordValid_of_data section14Catalog 6 _ hnum valid813
  · exact recordValid_of_data section14Catalog 6 _ hnum valid814
  · exact recordValid_of_data section14Catalog 6 _ hnum valid815
  · exact recordValid_of_data section14Catalog 6 _ hnum valid816
  · exact recordValid_of_data section14Catalog 6 _ hnum valid817
  · exact recordValid_of_data section14Catalog 6 _ hnum valid818
  · exact recordValid_of_data section14Catalog 6 _ hnum valid819
  · exact recordValid_of_data section14Catalog 6 _ hnum valid820
  · exact recordValid_of_data section14Catalog 6 _ hnum valid821
  · exact recordValid_of_data section14Catalog 6 _ hnum valid822
  · exact recordValid_of_data section14Catalog 6 _ hnum valid823
  · exact recordValid_of_data section14Catalog 6 _ hnum valid824
  · exact recordValid_of_data section14Catalog 6 _ hnum valid825
  · exact recordValid_of_data section14Catalog 6 _ hnum valid826
  · exact recordValid_of_data section14Catalog 6 _ hnum valid827
  · exact recordValid_of_data section14Catalog 6 _ hnum valid828
  · exact recordValid_of_data section14Catalog 6 _ hnum valid829
  · exact recordValid_of_data section14Catalog 6 _ hnum valid830
  · exact recordValid_of_data section14Catalog 6 _ hnum valid831
end Section14Records_6_800_832

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0800_0832


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0832_0864
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_832_864
private theorem valid832 : RecordDataValid section14Catalog 6 (⟨42,(7),[1,2,5,6,13,14],[174],288⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨288,[1,2,3,5,6,7,13,14,15],289⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid833 : RecordDataValid section14Catalog 6 (⟨42,(7),[1,2,5,6,13,14],[190],312⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨312,[1,2,4,5,6,8,13,14,16],313⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid834 : RecordDataValid section14Catalog 6 (⟨42,(7),[6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid835 : RecordDataValid section14Catalog 6 (⟨42,(8),[1,2,5,6,13,14],[170],255⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨255,[1,2,3,4,5,6,7,8,13,14,15,16],256⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid836 : RecordDataValid section14Catalog 6 (⟨42,(8),[1,2,5,6,13,14],[174],290⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨290,[1,2,3,5,6,7,13,14,15],291⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid837 : RecordDataValid section14Catalog 6 (⟨42,(8),[1,2,5,6,13,14],[190],314⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨314,[1,2,4,5,6,8,13,14,16],315⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid838 : RecordDataValid section14Catalog 6 (⟨42,(8),[6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid839 : RecordDataValid section14Catalog 6 (⟨42,(9),[1,2,5,6,13,14],[170],256⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨256,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],257⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid840 : RecordDataValid section14Catalog 6 (⟨42,(9),[1,2,5,6,13,14],[174],291⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨291,[1,2,3,5,6,7,13,14,15],292⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid841 : RecordDataValid section14Catalog 6 (⟨42,(9),[1,2,5,6,13,14],[190],315⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨315,[1,2,4,5,6,8,9,10,12,13,14,16],316⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid842 : RecordDataValid section14Catalog 6 (⟨42,(9),[6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid843 : RecordDataValid section14Catalog 6 (⟨42,(10),[1,2,5,6,13,14],[170],257⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨257,[1,2,3,4,5,6,7,8,13,14,15,16],258⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid844 : RecordDataValid section14Catalog 6 (⟨42,(10),[1,2,5,6,13,14],[174],292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨292,[1,2,3,5,6,7,13,14,15],293⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid845 : RecordDataValid section14Catalog 6 (⟨42,(10),[1,2,5,6,13,14],[190],316⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨316,[1,2,4,5,6,8,13,14,16],317⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid846 : RecordDataValid section14Catalog 6 (⟨42,(10),[6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid847 : RecordDataValid section14Catalog 6 (⟨42,(11),[1,2,5,6,13,14],[170],257⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨257,[1,2,3,4,5,6,7,8,13,14,15,16],258⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid848 : RecordDataValid section14Catalog 6 (⟨42,(11),[1,2,5,6,13,14],[174],292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨292,[1,2,3,5,6,7,13,14,15],293⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid849 : RecordDataValid section14Catalog 6 (⟨42,(11),[1,2,5,6,13,14],[190],316⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨316,[1,2,4,5,6,8,13,14,16],317⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid850 : RecordDataValid section14Catalog 6 (⟨42,(11),[6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid851 : RecordDataValid section14Catalog 6 (⟨42,(12),[1,2,5,6,13,14],[170],257⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨257,[1,2,3,4,5,6,7,8,13,14,15,16],258⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid852 : RecordDataValid section14Catalog 6 (⟨42,(12),[1,2,5,6,13,14],[174],292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨292,[1,2,3,5,6,7,13,14,15],293⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid853 : RecordDataValid section14Catalog 6 (⟨42,(12),[1,2,5,6,13,14],[190],316⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨316,[1,2,4,5,6,8,13,14,16],317⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid854 : RecordDataValid section14Catalog 6 (⟨42,(12),[6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid855 : RecordDataValid section14Catalog 6 (⟨42,(13),[1,2,5,6,13,14],[170],257⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨257,[1,2,3,4,5,6,7,8,13,14,15,16],258⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid856 : RecordDataValid section14Catalog 6 (⟨42,(13),[1,2,5,6,13,14],[174],292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨292,[1,2,3,5,6,7,13,14,15],293⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid857 : RecordDataValid section14Catalog 6 (⟨42,(13),[1,2,5,6,13,14],[190],316⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨316,[1,2,4,5,6,8,13,14,16],317⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid858 : RecordDataValid section14Catalog 6 (⟨42,(13),[6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid859 : RecordDataValid section14Catalog 6 (⟨42,(14),[1,2,5,6,13,14],[170],256⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨256,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],257⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid860 : RecordDataValid section14Catalog 6 (⟨42,(14),[1,2,5,6,13,14],[174],291⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨291,[1,2,3,5,6,7,13,14,15],292⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid861 : RecordDataValid section14Catalog 6 (⟨42,(14),[1,2,5,6,13,14],[190],315⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨315,[1,2,4,5,6,8,9,10,12,13,14,16],316⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid862 : RecordDataValid section14Catalog 6 (⟨42,(14),[6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid863 : RecordDataValid section14Catalog 6 (⟨42,(15),[1,2,5,6,13,14],[170],258⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨258,[1,2,3,4,5,6,7,8,13,14,15,16],259⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_0832_0864 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 832).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 832).take 32 = [⟨42,(7),[1,2,5,6,13,14],[174],288⟩,⟨42,(7),[1,2,5,6,13,14],[190],312⟩,⟨42,(7),[6],[150],3⟩,⟨42,(8),[1,2,5,6,13,14],[170],255⟩,⟨42,(8),[1,2,5,6,13,14],[174],290⟩,⟨42,(8),[1,2,5,6,13,14],[190],314⟩,⟨42,(8),[6],[150],3⟩,⟨42,(9),[1,2,5,6,13,14],[170],256⟩,⟨42,(9),[1,2,5,6,13,14],[174],291⟩,⟨42,(9),[1,2,5,6,13,14],[190],315⟩,⟨42,(9),[6],[150],3⟩,⟨42,(10),[1,2,5,6,13,14],[170],257⟩,⟨42,(10),[1,2,5,6,13,14],[174],292⟩,⟨42,(10),[1,2,5,6,13,14],[190],316⟩,⟨42,(10),[6],[150],3⟩,⟨42,(11),[1,2,5,6,13,14],[170],257⟩,⟨42,(11),[1,2,5,6,13,14],[174],292⟩,⟨42,(11),[1,2,5,6,13,14],[190],316⟩,⟨42,(11),[6],[150],3⟩,⟨42,(12),[1,2,5,6,13,14],[170],257⟩,⟨42,(12),[1,2,5,6,13,14],[174],292⟩,⟨42,(12),[1,2,5,6,13,14],[190],316⟩,⟨42,(12),[6],[150],3⟩,⟨42,(13),[1,2,5,6,13,14],[170],257⟩,⟨42,(13),[1,2,5,6,13,14],[174],292⟩,⟨42,(13),[1,2,5,6,13,14],[190],316⟩,⟨42,(13),[6],[150],3⟩,⟨42,(14),[1,2,5,6,13,14],[170],256⟩,⟨42,(14),[1,2,5,6,13,14],[174],291⟩,⟨42,(14),[1,2,5,6,13,14],[190],315⟩,⟨42,(14),[6],[150],3⟩,⟨42,(15),[1,2,5,6,13,14],[170],258⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid832
  · exact recordValid_of_data section14Catalog 6 _ hnum valid833
  · exact recordValid_of_data section14Catalog 6 _ hnum valid834
  · exact recordValid_of_data section14Catalog 6 _ hnum valid835
  · exact recordValid_of_data section14Catalog 6 _ hnum valid836
  · exact recordValid_of_data section14Catalog 6 _ hnum valid837
  · exact recordValid_of_data section14Catalog 6 _ hnum valid838
  · exact recordValid_of_data section14Catalog 6 _ hnum valid839
  · exact recordValid_of_data section14Catalog 6 _ hnum valid840
  · exact recordValid_of_data section14Catalog 6 _ hnum valid841
  · exact recordValid_of_data section14Catalog 6 _ hnum valid842
  · exact recordValid_of_data section14Catalog 6 _ hnum valid843
  · exact recordValid_of_data section14Catalog 6 _ hnum valid844
  · exact recordValid_of_data section14Catalog 6 _ hnum valid845
  · exact recordValid_of_data section14Catalog 6 _ hnum valid846
  · exact recordValid_of_data section14Catalog 6 _ hnum valid847
  · exact recordValid_of_data section14Catalog 6 _ hnum valid848
  · exact recordValid_of_data section14Catalog 6 _ hnum valid849
  · exact recordValid_of_data section14Catalog 6 _ hnum valid850
  · exact recordValid_of_data section14Catalog 6 _ hnum valid851
  · exact recordValid_of_data section14Catalog 6 _ hnum valid852
  · exact recordValid_of_data section14Catalog 6 _ hnum valid853
  · exact recordValid_of_data section14Catalog 6 _ hnum valid854
  · exact recordValid_of_data section14Catalog 6 _ hnum valid855
  · exact recordValid_of_data section14Catalog 6 _ hnum valid856
  · exact recordValid_of_data section14Catalog 6 _ hnum valid857
  · exact recordValid_of_data section14Catalog 6 _ hnum valid858
  · exact recordValid_of_data section14Catalog 6 _ hnum valid859
  · exact recordValid_of_data section14Catalog 6 _ hnum valid860
  · exact recordValid_of_data section14Catalog 6 _ hnum valid861
  · exact recordValid_of_data section14Catalog 6 _ hnum valid862
  · exact recordValid_of_data section14Catalog 6 _ hnum valid863
end Section14Records_6_832_864

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0832_0864


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0864_0896
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_864_896
private theorem valid864 : RecordDataValid section14Catalog 6 (⟨42,(15),[1,2,5,6,13,14],[174],293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨293,[1,2,3,5,6,7,13,14,15],294⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid865 : RecordDataValid section14Catalog 6 (⟨42,(15),[1,2,5,6,13,14],[190],317⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨317,[1,2,4,5,6,8,13,14,16],318⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid866 : RecordDataValid section14Catalog 6 (⟨42,(15),[6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid867 : RecordDataValid section14Catalog 6 (⟨42,(16),[1,2,5,6,13,14],[170],258⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨258,[1,2,3,4,5,6,7,8,13,14,15,16],259⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid868 : RecordDataValid section14Catalog 6 (⟨42,(16),[1,2,5,6,13,14],[174],293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨293,[1,2,3,5,6,7,13,14,15],294⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid869 : RecordDataValid section14Catalog 6 (⟨42,(16),[1,2,5,6,13,14],[190],317⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨317,[1,2,4,5,6,8,13,14,16],318⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid870 : RecordDataValid section14Catalog 6 (⟨42,(16),[6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid871 : RecordDataValid section14Catalog 6 (⟨42,(17),[1,2,5,6,13,14],[170],258⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨258,[1,2,3,4,5,6,7,8,13,14,15,16],259⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid872 : RecordDataValid section14Catalog 6 (⟨42,(17),[1,2,5,6,13,14],[174],293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨293,[1,2,3,5,6,7,13,14,15],294⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid873 : RecordDataValid section14Catalog 6 (⟨42,(17),[1,2,5,6,13,14],[190],317⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨317,[1,2,4,5,6,8,13,14,16],318⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid874 : RecordDataValid section14Catalog 6 (⟨42,(17),[6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid875 : RecordDataValid section14Catalog 6 (⟨42,(18),[1,2,5,6,13,14],[170],258⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨258,[1,2,3,4,5,6,7,8,13,14,15,16],259⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid876 : RecordDataValid section14Catalog 6 (⟨42,(18),[1,2,5,6,13,14],[174],293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨293,[1,2,3,5,6,7,13,14,15],294⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid877 : RecordDataValid section14Catalog 6 (⟨42,(18),[1,2,5,6,13,14],[190],317⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨317,[1,2,4,5,6,8,13,14,16],318⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid878 : RecordDataValid section14Catalog 6 (⟨42,(18),[6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid879 : RecordDataValid section14Catalog 6 (⟨42,(19),[1,2,5,6,13,14],[170],258⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨258,[1,2,3,4,5,6,7,8,13,14,15,16],259⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid880 : RecordDataValid section14Catalog 6 (⟨42,(19),[1,2,5,6,13,14],[174],293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨293,[1,2,3,5,6,7,13,14,15],294⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid881 : RecordDataValid section14Catalog 6 (⟨42,(19),[1,2,5,6,13,14],[190],317⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨317,[1,2,4,5,6,8,13,14,16],318⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid882 : RecordDataValid section14Catalog 6 (⟨42,(19),[6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid883 : RecordDataValid section14Catalog 6 (⟨42,(20),[1,2,5,6,13,14],[170],259⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨259,[1,2,3,4,5,6,7,8,13,14,15,16],260⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid884 : RecordDataValid section14Catalog 6 (⟨42,(20),[1,2,5,6,13,14],[174],294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨294,[1,2,3,5,6,7,13,14,15],295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid885 : RecordDataValid section14Catalog 6 (⟨42,(20),[1,2,5,6,13,14],[190],318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨318,[1,2,4,5,6,8,13,14,16],319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid886 : RecordDataValid section14Catalog 6 (⟨42,(20),[6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid887 : RecordDataValid section14Catalog 6 (⟨42,(21),[1,2,5,6,13,14],[170],259⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨259,[1,2,3,4,5,6,7,8,13,14,15,16],260⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid888 : RecordDataValid section14Catalog 6 (⟨42,(21),[1,2,5,6,13,14],[174],294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨294,[1,2,3,5,6,7,13,14,15],295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid889 : RecordDataValid section14Catalog 6 (⟨42,(21),[1,2,5,6,13,14],[190],318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨318,[1,2,4,5,6,8,13,14,16],319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid890 : RecordDataValid section14Catalog 6 (⟨42,(21),[6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid891 : RecordDataValid section14Catalog 6 (⟨42,(22),[1,2,5,6,13,14],[170],259⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨259,[1,2,3,4,5,6,7,8,13,14,15,16],260⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid892 : RecordDataValid section14Catalog 6 (⟨42,(22),[1,2,5,6,13,14],[174],294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨294,[1,2,3,5,6,7,13,14,15],295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid893 : RecordDataValid section14Catalog 6 (⟨42,(22),[1,2,5,6,13,14],[190],318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨318,[1,2,4,5,6,8,13,14,16],319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid894 : RecordDataValid section14Catalog 6 (⟨42,(22),[6],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid895 : RecordDataValid section14Catalog 6 (⟨42,(23),[1,2,5,6,13,14],[170],259⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨259,[1,2,3,4,5,6,7,8,13,14,15,16],260⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_0864_0896 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 864).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 864).take 32 = [⟨42,(15),[1,2,5,6,13,14],[174],293⟩,⟨42,(15),[1,2,5,6,13,14],[190],317⟩,⟨42,(15),[6],[150],3⟩,⟨42,(16),[1,2,5,6,13,14],[170],258⟩,⟨42,(16),[1,2,5,6,13,14],[174],293⟩,⟨42,(16),[1,2,5,6,13,14],[190],317⟩,⟨42,(16),[6],[150],3⟩,⟨42,(17),[1,2,5,6,13,14],[170],258⟩,⟨42,(17),[1,2,5,6,13,14],[174],293⟩,⟨42,(17),[1,2,5,6,13,14],[190],317⟩,⟨42,(17),[6],[150],3⟩,⟨42,(18),[1,2,5,6,13,14],[170],258⟩,⟨42,(18),[1,2,5,6,13,14],[174],293⟩,⟨42,(18),[1,2,5,6,13,14],[190],317⟩,⟨42,(18),[6],[150],3⟩,⟨42,(19),[1,2,5,6,13,14],[170],258⟩,⟨42,(19),[1,2,5,6,13,14],[174],293⟩,⟨42,(19),[1,2,5,6,13,14],[190],317⟩,⟨42,(19),[6],[150],3⟩,⟨42,(20),[1,2,5,6,13,14],[170],259⟩,⟨42,(20),[1,2,5,6,13,14],[174],294⟩,⟨42,(20),[1,2,5,6,13,14],[190],318⟩,⟨42,(20),[6],[150],3⟩,⟨42,(21),[1,2,5,6,13,14],[170],259⟩,⟨42,(21),[1,2,5,6,13,14],[174],294⟩,⟨42,(21),[1,2,5,6,13,14],[190],318⟩,⟨42,(21),[6],[150],3⟩,⟨42,(22),[1,2,5,6,13,14],[170],259⟩,⟨42,(22),[1,2,5,6,13,14],[174],294⟩,⟨42,(22),[1,2,5,6,13,14],[190],318⟩,⟨42,(22),[6],[150],3⟩,⟨42,(23),[1,2,5,6,13,14],[170],259⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid864
  · exact recordValid_of_data section14Catalog 6 _ hnum valid865
  · exact recordValid_of_data section14Catalog 6 _ hnum valid866
  · exact recordValid_of_data section14Catalog 6 _ hnum valid867
  · exact recordValid_of_data section14Catalog 6 _ hnum valid868
  · exact recordValid_of_data section14Catalog 6 _ hnum valid869
  · exact recordValid_of_data section14Catalog 6 _ hnum valid870
  · exact recordValid_of_data section14Catalog 6 _ hnum valid871
  · exact recordValid_of_data section14Catalog 6 _ hnum valid872
  · exact recordValid_of_data section14Catalog 6 _ hnum valid873
  · exact recordValid_of_data section14Catalog 6 _ hnum valid874
  · exact recordValid_of_data section14Catalog 6 _ hnum valid875
  · exact recordValid_of_data section14Catalog 6 _ hnum valid876
  · exact recordValid_of_data section14Catalog 6 _ hnum valid877
  · exact recordValid_of_data section14Catalog 6 _ hnum valid878
  · exact recordValid_of_data section14Catalog 6 _ hnum valid879
  · exact recordValid_of_data section14Catalog 6 _ hnum valid880
  · exact recordValid_of_data section14Catalog 6 _ hnum valid881
  · exact recordValid_of_data section14Catalog 6 _ hnum valid882
  · exact recordValid_of_data section14Catalog 6 _ hnum valid883
  · exact recordValid_of_data section14Catalog 6 _ hnum valid884
  · exact recordValid_of_data section14Catalog 6 _ hnum valid885
  · exact recordValid_of_data section14Catalog 6 _ hnum valid886
  · exact recordValid_of_data section14Catalog 6 _ hnum valid887
  · exact recordValid_of_data section14Catalog 6 _ hnum valid888
  · exact recordValid_of_data section14Catalog 6 _ hnum valid889
  · exact recordValid_of_data section14Catalog 6 _ hnum valid890
  · exact recordValid_of_data section14Catalog 6 _ hnum valid891
  · exact recordValid_of_data section14Catalog 6 _ hnum valid892
  · exact recordValid_of_data section14Catalog 6 _ hnum valid893
  · exact recordValid_of_data section14Catalog 6 _ hnum valid894
  · exact recordValid_of_data section14Catalog 6 _ hnum valid895
end Section14Records_6_864_896

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0864_0896

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 768).take 128, section14RecordValid section14Catalog 6 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (6 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 6 r
  exact (all_of_interval_split P xs 768 832 896 (by decide) (by decide) (all_of_interval_split P xs 768 800 832 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_0768_0800 hnum) (Freiman.workReverse20260919_s0006_records_0800_0832 hnum)) (all_of_interval_split P xs 832 864 896 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_0832_0864 hnum) (Freiman.workReverse20260919_s0006_records_0864_0896 hnum)))

#print axioms solution
