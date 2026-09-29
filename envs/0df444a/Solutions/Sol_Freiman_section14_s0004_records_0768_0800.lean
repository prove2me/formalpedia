-- Prove2me | solution 1 for Freiman.section14_s0004_records_0768_0800
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T02:18:52.947179+00:00
-- url     : https://prove2.me/submissions/4ca0aded-31ee-4597-ab8c-9a873bad0628

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
namespace Section14Records_4_768_800
private theorem valid768 : RecordDataValid section14Catalog 4 (⟨111,(11),[4,8,12,16],[10],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid769 : RecordDataValid section14Catalog 4 (⟨111,(12),[4,8,12,16],[10],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid770 : RecordDataValid section14Catalog 4 (⟨111,(13),[4,8,12,16],[10],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid771 : RecordDataValid section14Catalog 4 (⟨111,(14),[4,8,12,16],[10],456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨456,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid772 : RecordDataValid section14Catalog 4 (⟨111,(15),[4,8,12,16],[10],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid773 : RecordDataValid section14Catalog 4 (⟨111,(16),[4,8,12,16],[10],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid774 : RecordDataValid section14Catalog 4 (⟨111,(17),[4,8,12,16],[10],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid775 : RecordDataValid section14Catalog 4 (⟨111,(18),[4,8,12,16],[10],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid776 : RecordDataValid section14Catalog 4 (⟨111,(19),[4,8,12,16],[10],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid777 : RecordDataValid section14Catalog 4 (⟨111,(20),[4,8,12,16],[10],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid778 : RecordDataValid section14Catalog 4 (⟨111,(21),[4,8,12,16],[10],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid779 : RecordDataValid section14Catalog 4 (⟨111,(22),[4,8,12,16],[10],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid780 : RecordDataValid section14Catalog 4 (⟨111,(23),[4,8,12,16],[10],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid781 : RecordDataValid section14Catalog 4 (⟨111,(24),[4,8,12,16],[10],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid782 : RecordDataValid section14Catalog 4 (⟨114,(0),[4,8,12,16],[10],460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨460,[1,4,5,6,8,9,10,12,13,16],461⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid783 : RecordDataValid section14Catalog 4 (⟨114,(1),[4,8,12,16],[10],460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨460,[1,4,5,6,8,9,10,12,13,16],461⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid784 : RecordDataValid section14Catalog 4 (⟨114,(2),[4,8,12,16],[10],460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨460,[1,4,5,6,8,9,10,12,13,16],461⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid785 : RecordDataValid section14Catalog 4 (⟨114,(3),[4,8,12,16],[10],460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨460,[1,4,5,6,8,9,10,12,13,16],461⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid786 : RecordDataValid section14Catalog 4 (⟨114,(4),[4,8,12,16],[10],460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨460,[1,4,5,6,8,9,10,12,13,16],461⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid787 : RecordDataValid section14Catalog 4 (⟨114,(5),[4,8,12,16],[10],461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨461,[1,4,5,6,8,9,10,12,13,16],462⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid788 : RecordDataValid section14Catalog 4 (⟨114,(6),[4,8,12,16],[10],461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨461,[1,4,5,6,8,9,10,12,13,16],462⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid789 : RecordDataValid section14Catalog 4 (⟨114,(7),[4,8,12,16],[10],461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨461,[1,4,5,6,8,9,10,12,13,16],462⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid790 : RecordDataValid section14Catalog 4 (⟨114,(8),[4,8,12,16],[10],461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨461,[1,4,5,6,8,9,10,12,13,16],462⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid791 : RecordDataValid section14Catalog 4 (⟨114,(9),[4,8,12,16],[10],461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨461,[1,4,5,6,8,9,10,12,13,16],462⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid792 : RecordDataValid section14Catalog 4 (⟨114,(10),[4,8,12,16],[10],462⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨462,[1,4,5,6,8,9,10,12,13,16],463⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid793 : RecordDataValid section14Catalog 4 (⟨114,(11),[4,8,12,16],[10],463⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨463,[1,4,5,6,8,9,10,12,13,16],464⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid794 : RecordDataValid section14Catalog 4 (⟨114,(12),[4,8,12,16],[10],464⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨464,[1,4,5,6,8,9,10,12,13,16],465⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid795 : RecordDataValid section14Catalog 4 (⟨114,(13),[4,8,12,16],[10],463⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨463,[1,4,5,6,8,9,10,12,13,16],464⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid796 : RecordDataValid section14Catalog 4 (⟨114,(14),[4,8,12,16],[10],465⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨465,[1,4,5,6,8,9,10,12,13,16],466⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid797 : RecordDataValid section14Catalog 4 (⟨114,(15),[4,8,12,16],[10],462⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨462,[1,4,5,6,8,9,10,12,13,16],463⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid798 : RecordDataValid section14Catalog 4 (⟨114,(16),[4,8,12,16],[10],466⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨466,[1,4,5,6,8,9,10,12,13,16],467⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid799 : RecordDataValid section14Catalog 4 (⟨114,(17),[4,8,12,16],[10],466⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨466,[1,4,5,6,8,9,10,12,13,16],467⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 768).take 32, section14RecordValid section14Catalog 4 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (4 ∈ r.states))).drop 768).take 32 = [⟨111,(11),[4,8,12,16],[10],457⟩,⟨111,(12),[4,8,12,16],[10],457⟩,⟨111,(13),[4,8,12,16],[10],457⟩,⟨111,(14),[4,8,12,16],[10],456⟩,⟨111,(15),[4,8,12,16],[10],458⟩,⟨111,(16),[4,8,12,16],[10],458⟩,⟨111,(17),[4,8,12,16],[10],458⟩,⟨111,(18),[4,8,12,16],[10],458⟩,⟨111,(19),[4,8,12,16],[10],458⟩,⟨111,(20),[4,8,12,16],[10],459⟩,⟨111,(21),[4,8,12,16],[10],459⟩,⟨111,(22),[4,8,12,16],[10],459⟩,⟨111,(23),[4,8,12,16],[10],459⟩,⟨111,(24),[4,8,12,16],[10],459⟩,⟨114,(0),[4,8,12,16],[10],460⟩,⟨114,(1),[4,8,12,16],[10],460⟩,⟨114,(2),[4,8,12,16],[10],460⟩,⟨114,(3),[4,8,12,16],[10],460⟩,⟨114,(4),[4,8,12,16],[10],460⟩,⟨114,(5),[4,8,12,16],[10],461⟩,⟨114,(6),[4,8,12,16],[10],461⟩,⟨114,(7),[4,8,12,16],[10],461⟩,⟨114,(8),[4,8,12,16],[10],461⟩,⟨114,(9),[4,8,12,16],[10],461⟩,⟨114,(10),[4,8,12,16],[10],462⟩,⟨114,(11),[4,8,12,16],[10],463⟩,⟨114,(12),[4,8,12,16],[10],464⟩,⟨114,(13),[4,8,12,16],[10],463⟩,⟨114,(14),[4,8,12,16],[10],465⟩,⟨114,(15),[4,8,12,16],[10],462⟩,⟨114,(16),[4,8,12,16],[10],466⟩,⟨114,(17),[4,8,12,16],[10],466⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 4 _ hnum valid768
  · exact recordValid_of_data section14Catalog 4 _ hnum valid769
  · exact recordValid_of_data section14Catalog 4 _ hnum valid770
  · exact recordValid_of_data section14Catalog 4 _ hnum valid771
  · exact recordValid_of_data section14Catalog 4 _ hnum valid772
  · exact recordValid_of_data section14Catalog 4 _ hnum valid773
  · exact recordValid_of_data section14Catalog 4 _ hnum valid774
  · exact recordValid_of_data section14Catalog 4 _ hnum valid775
  · exact recordValid_of_data section14Catalog 4 _ hnum valid776
  · exact recordValid_of_data section14Catalog 4 _ hnum valid777
  · exact recordValid_of_data section14Catalog 4 _ hnum valid778
  · exact recordValid_of_data section14Catalog 4 _ hnum valid779
  · exact recordValid_of_data section14Catalog 4 _ hnum valid780
  · exact recordValid_of_data section14Catalog 4 _ hnum valid781
  · exact recordValid_of_data section14Catalog 4 _ hnum valid782
  · exact recordValid_of_data section14Catalog 4 _ hnum valid783
  · exact recordValid_of_data section14Catalog 4 _ hnum valid784
  · exact recordValid_of_data section14Catalog 4 _ hnum valid785
  · exact recordValid_of_data section14Catalog 4 _ hnum valid786
  · exact recordValid_of_data section14Catalog 4 _ hnum valid787
  · exact recordValid_of_data section14Catalog 4 _ hnum valid788
  · exact recordValid_of_data section14Catalog 4 _ hnum valid789
  · exact recordValid_of_data section14Catalog 4 _ hnum valid790
  · exact recordValid_of_data section14Catalog 4 _ hnum valid791
  · exact recordValid_of_data section14Catalog 4 _ hnum valid792
  · exact recordValid_of_data section14Catalog 4 _ hnum valid793
  · exact recordValid_of_data section14Catalog 4 _ hnum valid794
  · exact recordValid_of_data section14Catalog 4 _ hnum valid795
  · exact recordValid_of_data section14Catalog 4 _ hnum valid796
  · exact recordValid_of_data section14Catalog 4 _ hnum valid797
  · exact recordValid_of_data section14Catalog 4 _ hnum valid798
  · exact recordValid_of_data section14Catalog 4 _ hnum valid799
end Section14Records_4_768_800

#print axioms solution
