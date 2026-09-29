-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_0768_0896
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:10:20.218114+00:00
-- url     : https://prove2.me/submissions/40b2a7e8-a5fd-4f9e-b4dc-3deedf9adc90

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_0768_0800
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_768_800
private theorem valid768 : RecordDataValid section14Catalog 5 (⟨28,(16),[1,5],[134,135],138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨138,[1,2,3,5,6,7],138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid769 : RecordDataValid section14Catalog 5 (⟨28,(16),[5],[146],180⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨180,[1,5,9,10],180⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid770 : RecordDataValid section14Catalog 5 (⟨28,(17),[1,2,5,6],[131],119⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨119,[1,2,3,5,6,7,9,10,11],119⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid771 : RecordDataValid section14Catalog 5 (⟨28,(17),[1,2,5,6],[150],138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨138,[1,2,3,5,6,7],138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid772 : RecordDataValid section14Catalog 5 (⟨28,(17),[1,5],[130],91⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨91,[1,5,9],91⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid773 : RecordDataValid section14Catalog 5 (⟨28,(17),[1,5],[134,135],138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨138,[1,2,3,5,6,7],138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid774 : RecordDataValid section14Catalog 5 (⟨28,(17),[5],[146],180⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨180,[1,5,9,10],180⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid775 : RecordDataValid section14Catalog 5 (⟨28,(18),[1,2,5,6],[131],119⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨119,[1,2,3,5,6,7,9,10,11],119⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid776 : RecordDataValid section14Catalog 5 (⟨28,(18),[1,2,5,6],[150],138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨138,[1,2,3,5,6,7],138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid777 : RecordDataValid section14Catalog 5 (⟨28,(18),[1,5],[130],91⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨91,[1,5,9],91⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid778 : RecordDataValid section14Catalog 5 (⟨28,(18),[1,5],[134,135],138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨138,[1,2,3,5,6,7],138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid779 : RecordDataValid section14Catalog 5 (⟨28,(18),[5],[146],180⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨180,[1,5,9,10],180⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid780 : RecordDataValid section14Catalog 5 (⟨28,(19),[1,2,5,6],[131],119⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨119,[1,2,3,5,6,7,9,10,11],119⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid781 : RecordDataValid section14Catalog 5 (⟨28,(19),[1,2,5,6],[150],138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨138,[1,2,3,5,6,7],138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid782 : RecordDataValid section14Catalog 5 (⟨28,(19),[1,5],[130],91⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨91,[1,5,9],91⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid783 : RecordDataValid section14Catalog 5 (⟨28,(19),[1,5],[134,135],138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨138,[1,2,3,5,6,7],138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid784 : RecordDataValid section14Catalog 5 (⟨28,(19),[5],[146],180⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨180,[1,5,9,10],180⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid785 : RecordDataValid section14Catalog 5 (⟨28,(20),[1,2,5,6],[131],115⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨115,[1,2,3,5,6,7,9,10,11],115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid786 : RecordDataValid section14Catalog 5 (⟨28,(20),[1,2,5,6],[150],134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨134,[1,2,3,5,6,7],134⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid787 : RecordDataValid section14Catalog 5 (⟨28,(20),[1,5],[130],87⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨87,[1,5,9],87⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid788 : RecordDataValid section14Catalog 5 (⟨28,(20),[1,5],[134,135],134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨134,[1,2,3,5,6,7],134⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid789 : RecordDataValid section14Catalog 5 (⟨28,(20),[5],[146],176⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨176,[1,5,9,10],176⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid790 : RecordDataValid section14Catalog 5 (⟨28,(21),[1,2,5,6],[131],116⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨116,[1,2,5,6,9,10],116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid791 : RecordDataValid section14Catalog 5 (⟨28,(21),[1,2,5,6],[150],135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨135,[1,2,5,6],135⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid792 : RecordDataValid section14Catalog 5 (⟨28,(21),[1,5],[130],88⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨88,[1,5,9],88⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid793 : RecordDataValid section14Catalog 5 (⟨28,(21),[1,5],[134,135],135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨135,[1,2,5,6],135⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid794 : RecordDataValid section14Catalog 5 (⟨28,(21),[5],[146],177⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨177,[1,5,9,10],177⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid795 : RecordDataValid section14Catalog 5 (⟨28,(22),[1,2,5,6],[131],117⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨117,[1,2,3,5,6,7,9,10,11],117⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid796 : RecordDataValid section14Catalog 5 (⟨28,(22),[1,2,5,6],[150],136⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨136,[1,2,3,5,6,7],136⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid797 : RecordDataValid section14Catalog 5 (⟨28,(22),[1,5],[130],89⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨89,[1,5,9],89⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid798 : RecordDataValid section14Catalog 5 (⟨28,(22),[1,5],[134,135],136⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨136,[1,2,3,5,6,7],136⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid799 : RecordDataValid section14Catalog 5 (⟨28,(22),[5],[146],178⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨178,[1,5,9,10],178⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_0768_0800 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 768).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 768).take 32 = [⟨28,(16),[1,5],[134,135],138⟩,⟨28,(16),[5],[146],180⟩,⟨28,(17),[1,2,5,6],[131],119⟩,⟨28,(17),[1,2,5,6],[150],138⟩,⟨28,(17),[1,5],[130],91⟩,⟨28,(17),[1,5],[134,135],138⟩,⟨28,(17),[5],[146],180⟩,⟨28,(18),[1,2,5,6],[131],119⟩,⟨28,(18),[1,2,5,6],[150],138⟩,⟨28,(18),[1,5],[130],91⟩,⟨28,(18),[1,5],[134,135],138⟩,⟨28,(18),[5],[146],180⟩,⟨28,(19),[1,2,5,6],[131],119⟩,⟨28,(19),[1,2,5,6],[150],138⟩,⟨28,(19),[1,5],[130],91⟩,⟨28,(19),[1,5],[134,135],138⟩,⟨28,(19),[5],[146],180⟩,⟨28,(20),[1,2,5,6],[131],115⟩,⟨28,(20),[1,2,5,6],[150],134⟩,⟨28,(20),[1,5],[130],87⟩,⟨28,(20),[1,5],[134,135],134⟩,⟨28,(20),[5],[146],176⟩,⟨28,(21),[1,2,5,6],[131],116⟩,⟨28,(21),[1,2,5,6],[150],135⟩,⟨28,(21),[1,5],[130],88⟩,⟨28,(21),[1,5],[134,135],135⟩,⟨28,(21),[5],[146],177⟩,⟨28,(22),[1,2,5,6],[131],117⟩,⟨28,(22),[1,2,5,6],[150],136⟩,⟨28,(22),[1,5],[130],89⟩,⟨28,(22),[1,5],[134,135],136⟩,⟨28,(22),[5],[146],178⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid768
  · exact recordValid_of_data section14Catalog 5 _ hnum valid769
  · exact recordValid_of_data section14Catalog 5 _ hnum valid770
  · exact recordValid_of_data section14Catalog 5 _ hnum valid771
  · exact recordValid_of_data section14Catalog 5 _ hnum valid772
  · exact recordValid_of_data section14Catalog 5 _ hnum valid773
  · exact recordValid_of_data section14Catalog 5 _ hnum valid774
  · exact recordValid_of_data section14Catalog 5 _ hnum valid775
  · exact recordValid_of_data section14Catalog 5 _ hnum valid776
  · exact recordValid_of_data section14Catalog 5 _ hnum valid777
  · exact recordValid_of_data section14Catalog 5 _ hnum valid778
  · exact recordValid_of_data section14Catalog 5 _ hnum valid779
  · exact recordValid_of_data section14Catalog 5 _ hnum valid780
  · exact recordValid_of_data section14Catalog 5 _ hnum valid781
  · exact recordValid_of_data section14Catalog 5 _ hnum valid782
  · exact recordValid_of_data section14Catalog 5 _ hnum valid783
  · exact recordValid_of_data section14Catalog 5 _ hnum valid784
  · exact recordValid_of_data section14Catalog 5 _ hnum valid785
  · exact recordValid_of_data section14Catalog 5 _ hnum valid786
  · exact recordValid_of_data section14Catalog 5 _ hnum valid787
  · exact recordValid_of_data section14Catalog 5 _ hnum valid788
  · exact recordValid_of_data section14Catalog 5 _ hnum valid789
  · exact recordValid_of_data section14Catalog 5 _ hnum valid790
  · exact recordValid_of_data section14Catalog 5 _ hnum valid791
  · exact recordValid_of_data section14Catalog 5 _ hnum valid792
  · exact recordValid_of_data section14Catalog 5 _ hnum valid793
  · exact recordValid_of_data section14Catalog 5 _ hnum valid794
  · exact recordValid_of_data section14Catalog 5 _ hnum valid795
  · exact recordValid_of_data section14Catalog 5 _ hnum valid796
  · exact recordValid_of_data section14Catalog 5 _ hnum valid797
  · exact recordValid_of_data section14Catalog 5 _ hnum valid798
  · exact recordValid_of_data section14Catalog 5 _ hnum valid799
end Section14Records_5_768_800

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_0768_0800


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_0800_0832
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_800_832
private theorem valid800 : RecordDataValid section14Catalog 5 (⟨28,(23),[1,2,5,6],[131],116⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨116,[1,2,5,6,9,10],116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid801 : RecordDataValid section14Catalog 5 (⟨28,(23),[1,2,5,6],[150],135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨135,[1,2,5,6],135⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid802 : RecordDataValid section14Catalog 5 (⟨28,(23),[1,5],[130],88⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨88,[1,5,9],88⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid803 : RecordDataValid section14Catalog 5 (⟨28,(23),[1,5],[134,135],135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨135,[1,2,5,6],135⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid804 : RecordDataValid section14Catalog 5 (⟨28,(23),[5],[146],177⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨177,[1,5,9,10],177⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid805 : RecordDataValid section14Catalog 5 (⟨28,(24),[1,2,5,6],[131],118⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨118,[1,2,5,6,9,10],118⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid806 : RecordDataValid section14Catalog 5 (⟨28,(24),[1,2,5,6],[150],137⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨137,[1,2,5,6],137⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid807 : RecordDataValid section14Catalog 5 (⟨28,(24),[1,5],[130],90⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨90,[1,5,9],90⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid808 : RecordDataValid section14Catalog 5 (⟨28,(24),[1,5],[134,135],137⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨137,[1,2,5,6],137⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid809 : RecordDataValid section14Catalog 5 (⟨28,(24),[5],[146],179⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨179,[1,5,9,10],179⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid810 : RecordDataValid section14Catalog 5 (⟨30,(0),[1,2,5,6],[146,150],152⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨152,[1,2,3,4,5,6,7,8,9,10,11,12],152⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid811 : RecordDataValid section14Catalog 5 (⟨30,(0),[5],[131,134,135],152⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨152,[1,2,3,4,5,6,7,8,9,10,11,12],152⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid812 : RecordDataValid section14Catalog 5 (⟨30,(0),[5,6],[130],152⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨152,[1,2,3,4,5,6,7,8,9,10,11,12],152⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid813 : RecordDataValid section14Catalog 5 (⟨30,(1),[1,2,5,6],[146,150],153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨153,[1,2,3,4,5,6,7,8,9,10,11,12],153⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid814 : RecordDataValid section14Catalog 5 (⟨30,(1),[5],[131,134,135],153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨153,[1,2,3,4,5,6,7,8,9,10,11,12],153⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid815 : RecordDataValid section14Catalog 5 (⟨30,(1),[5,6],[130],153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨153,[1,2,3,4,5,6,7,8,9,10,11,12],153⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid816 : RecordDataValid section14Catalog 5 (⟨30,(2),[1,2,5,6],[130],92⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨92,[1,2,5,6,9,10,12],92⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid817 : RecordDataValid section14Catalog 5 (⟨30,(2),[1,2,5,6],[146],154⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨154,[1,2,3,5,6,7],154⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid818 : RecordDataValid section14Catalog 5 (⟨30,(2),[1,2,5,6],[150],200⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨200,[1,2,3,4,5,6,7,8,9,10,11,12],200⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid819 : RecordDataValid section14Catalog 5 (⟨30,(2),[1,5],[134],92⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨92,[1,2,5,6,9,10,12],92⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid820 : RecordDataValid section14Catalog 5 (⟨30,(2),[1,5],[135],120⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨120,[1,2,5,6,9,10],120⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid821 : RecordDataValid section14Catalog 5 (⟨30,(2),[1,5,6],[131],120⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨120,[1,2,5,6,9,10],120⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid822 : RecordDataValid section14Catalog 5 (⟨30,(3),[1,2,5,6],[130],93⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨93,[1,2,5,6,9,10,12],93⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid823 : RecordDataValid section14Catalog 5 (⟨30,(3),[1,2,5,6],[146],155⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨155,[1,2,3,5,6,7],155⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid824 : RecordDataValid section14Catalog 5 (⟨30,(3),[1,5],[134],93⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨93,[1,2,5,6,9,10,12],93⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid825 : RecordDataValid section14Catalog 5 (⟨30,(3),[5],[135],181⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨181,[1,2,5,6,9,10],181⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid826 : RecordDataValid section14Catalog 5 (⟨30,(3),[5,6],[131],181⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨181,[1,2,5,6,9,10],181⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid827 : RecordDataValid section14Catalog 5 (⟨30,(3),[5,6],[150],230⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨230,[1,2,3,4,5,6,7,8,9,10,11,12],230⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid828 : RecordDataValid section14Catalog 5 (⟨30,(4),[1,2,5,6],[130],94⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨94,[1,2,5,6,9,10,12],94⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid829 : RecordDataValid section14Catalog 5 (⟨30,(4),[1,2,5,6],[146],156⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨156,[1,2,3,5,6,7],156⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid830 : RecordDataValid section14Catalog 5 (⟨30,(4),[1,5],[134],94⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨94,[1,2,5,6,9,10,12],94⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid831 : RecordDataValid section14Catalog 5 (⟨30,(4),[5],[135],182⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨182,[1,2,5,6,9,10],182⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_0800_0832 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 800).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 800).take 32 = [⟨28,(23),[1,2,5,6],[131],116⟩,⟨28,(23),[1,2,5,6],[150],135⟩,⟨28,(23),[1,5],[130],88⟩,⟨28,(23),[1,5],[134,135],135⟩,⟨28,(23),[5],[146],177⟩,⟨28,(24),[1,2,5,6],[131],118⟩,⟨28,(24),[1,2,5,6],[150],137⟩,⟨28,(24),[1,5],[130],90⟩,⟨28,(24),[1,5],[134,135],137⟩,⟨28,(24),[5],[146],179⟩,⟨30,(0),[1,2,5,6],[146,150],152⟩,⟨30,(0),[5],[131,134,135],152⟩,⟨30,(0),[5,6],[130],152⟩,⟨30,(1),[1,2,5,6],[146,150],153⟩,⟨30,(1),[5],[131,134,135],153⟩,⟨30,(1),[5,6],[130],153⟩,⟨30,(2),[1,2,5,6],[130],92⟩,⟨30,(2),[1,2,5,6],[146],154⟩,⟨30,(2),[1,2,5,6],[150],200⟩,⟨30,(2),[1,5],[134],92⟩,⟨30,(2),[1,5],[135],120⟩,⟨30,(2),[1,5,6],[131],120⟩,⟨30,(3),[1,2,5,6],[130],93⟩,⟨30,(3),[1,2,5,6],[146],155⟩,⟨30,(3),[1,5],[134],93⟩,⟨30,(3),[5],[135],181⟩,⟨30,(3),[5,6],[131],181⟩,⟨30,(3),[5,6],[150],230⟩,⟨30,(4),[1,2,5,6],[130],94⟩,⟨30,(4),[1,2,5,6],[146],156⟩,⟨30,(4),[1,5],[134],94⟩,⟨30,(4),[5],[135],182⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid800
  · exact recordValid_of_data section14Catalog 5 _ hnum valid801
  · exact recordValid_of_data section14Catalog 5 _ hnum valid802
  · exact recordValid_of_data section14Catalog 5 _ hnum valid803
  · exact recordValid_of_data section14Catalog 5 _ hnum valid804
  · exact recordValid_of_data section14Catalog 5 _ hnum valid805
  · exact recordValid_of_data section14Catalog 5 _ hnum valid806
  · exact recordValid_of_data section14Catalog 5 _ hnum valid807
  · exact recordValid_of_data section14Catalog 5 _ hnum valid808
  · exact recordValid_of_data section14Catalog 5 _ hnum valid809
  · exact recordValid_of_data section14Catalog 5 _ hnum valid810
  · exact recordValid_of_data section14Catalog 5 _ hnum valid811
  · exact recordValid_of_data section14Catalog 5 _ hnum valid812
  · exact recordValid_of_data section14Catalog 5 _ hnum valid813
  · exact recordValid_of_data section14Catalog 5 _ hnum valid814
  · exact recordValid_of_data section14Catalog 5 _ hnum valid815
  · exact recordValid_of_data section14Catalog 5 _ hnum valid816
  · exact recordValid_of_data section14Catalog 5 _ hnum valid817
  · exact recordValid_of_data section14Catalog 5 _ hnum valid818
  · exact recordValid_of_data section14Catalog 5 _ hnum valid819
  · exact recordValid_of_data section14Catalog 5 _ hnum valid820
  · exact recordValid_of_data section14Catalog 5 _ hnum valid821
  · exact recordValid_of_data section14Catalog 5 _ hnum valid822
  · exact recordValid_of_data section14Catalog 5 _ hnum valid823
  · exact recordValid_of_data section14Catalog 5 _ hnum valid824
  · exact recordValid_of_data section14Catalog 5 _ hnum valid825
  · exact recordValid_of_data section14Catalog 5 _ hnum valid826
  · exact recordValid_of_data section14Catalog 5 _ hnum valid827
  · exact recordValid_of_data section14Catalog 5 _ hnum valid828
  · exact recordValid_of_data section14Catalog 5 _ hnum valid829
  · exact recordValid_of_data section14Catalog 5 _ hnum valid830
  · exact recordValid_of_data section14Catalog 5 _ hnum valid831
end Section14Records_5_800_832

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_0800_0832


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_0832_0864
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_832_864
private theorem valid832 : RecordDataValid section14Catalog 5 (⟨30,(4),[5,6],[131],182⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨182,[1,2,5,6,9,10],182⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid833 : RecordDataValid section14Catalog 5 (⟨30,(4),[5,6],[150],231⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨231,[1,2,3,4,5,6,7,8,9,10,11,12],231⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid834 : RecordDataValid section14Catalog 5 (⟨30,(5),[1,2,5,6],[130],93⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨93,[1,2,5,6,9,10,12],93⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid835 : RecordDataValid section14Catalog 5 (⟨30,(5),[1,2,5,6],[146],155⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨155,[1,2,3,5,6,7],155⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid836 : RecordDataValid section14Catalog 5 (⟨30,(5),[1,5],[134],93⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨93,[1,2,5,6,9,10,12],93⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid837 : RecordDataValid section14Catalog 5 (⟨30,(5),[5],[135],181⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨181,[1,2,5,6,9,10],181⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid838 : RecordDataValid section14Catalog 5 (⟨30,(5),[5,6],[131],181⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨181,[1,2,5,6,9,10],181⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid839 : RecordDataValid section14Catalog 5 (⟨30,(5),[5,6],[150],230⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨230,[1,2,3,4,5,6,7,8,9,10,11,12],230⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid840 : RecordDataValid section14Catalog 5 (⟨30,(6),[1,2,5,6],[130],95⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨95,[1,2,5,6,9,10,12],95⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid841 : RecordDataValid section14Catalog 5 (⟨30,(6),[1,2,5,6],[146],157⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨157,[1,2,3,5,6,7],157⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid842 : RecordDataValid section14Catalog 5 (⟨30,(6),[1,5],[134],95⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨95,[1,2,5,6,9,10,12],95⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid843 : RecordDataValid section14Catalog 5 (⟨30,(6),[5],[135],183⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨183,[1,2,5,6,9,10],183⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid844 : RecordDataValid section14Catalog 5 (⟨30,(6),[5,6],[131],183⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨183,[1,2,5,6,9,10],183⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid845 : RecordDataValid section14Catalog 5 (⟨30,(6),[5,6],[150],232⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨232,[1,2,3,4,5,6,7,8,9,10,11,12],232⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid846 : RecordDataValid section14Catalog 5 (⟨30,(7),[1,2,5,6],[130],95⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨95,[1,2,5,6,9,10,12],95⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid847 : RecordDataValid section14Catalog 5 (⟨30,(7),[1,2,5,6],[146],157⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨157,[1,2,3,5,6,7],157⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid848 : RecordDataValid section14Catalog 5 (⟨30,(7),[1,5],[134],95⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨95,[1,2,5,6,9,10,12],95⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid849 : RecordDataValid section14Catalog 5 (⟨30,(7),[5],[135],183⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨183,[1,2,5,6,9,10],183⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid850 : RecordDataValid section14Catalog 5 (⟨30,(7),[5,6],[131],183⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨183,[1,2,5,6,9,10],183⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid851 : RecordDataValid section14Catalog 5 (⟨30,(7),[5,6],[150],232⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨232,[1,2,3,4,5,6,7,8,9,10,11,12],232⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid852 : RecordDataValid section14Catalog 5 (⟨30,(8),[1,2,5,6],[130],96⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨96,[1,2,5,6,9,10,12],96⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid853 : RecordDataValid section14Catalog 5 (⟨30,(8),[1,2,5,6],[146],158⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨158,[1,2,3,5,6,7],158⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid854 : RecordDataValid section14Catalog 5 (⟨30,(8),[1,5],[134],96⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨96,[1,2,5,6,9,10,12],96⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid855 : RecordDataValid section14Catalog 5 (⟨30,(8),[5],[135],184⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨184,[1,2,5,6,9,10],184⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid856 : RecordDataValid section14Catalog 5 (⟨30,(8),[5,6],[131],184⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨184,[1,2,5,6,9,10],184⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid857 : RecordDataValid section14Catalog 5 (⟨30,(8),[5,6],[150],233⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨233,[1,2,3,4,5,6,7,8,9,10,11,12],233⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid858 : RecordDataValid section14Catalog 5 (⟨30,(9),[1,2,5,6],[130],96⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨96,[1,2,5,6,9,10,12],96⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid859 : RecordDataValid section14Catalog 5 (⟨30,(9),[1,2,5,6],[146],158⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨158,[1,2,3,5,6,7],158⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid860 : RecordDataValid section14Catalog 5 (⟨30,(9),[1,5],[134],96⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨96,[1,2,5,6,9,10,12],96⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid861 : RecordDataValid section14Catalog 5 (⟨30,(9),[5],[135],184⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨184,[1,2,5,6,9,10],184⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid862 : RecordDataValid section14Catalog 5 (⟨30,(9),[5,6],[131],184⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨184,[1,2,5,6,9,10],184⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid863 : RecordDataValid section14Catalog 5 (⟨30,(9),[5,6],[150],233⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨233,[1,2,3,4,5,6,7,8,9,10,11,12],233⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_0832_0864 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 832).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 832).take 32 = [⟨30,(4),[5,6],[131],182⟩,⟨30,(4),[5,6],[150],231⟩,⟨30,(5),[1,2,5,6],[130],93⟩,⟨30,(5),[1,2,5,6],[146],155⟩,⟨30,(5),[1,5],[134],93⟩,⟨30,(5),[5],[135],181⟩,⟨30,(5),[5,6],[131],181⟩,⟨30,(5),[5,6],[150],230⟩,⟨30,(6),[1,2,5,6],[130],95⟩,⟨30,(6),[1,2,5,6],[146],157⟩,⟨30,(6),[1,5],[134],95⟩,⟨30,(6),[5],[135],183⟩,⟨30,(6),[5,6],[131],183⟩,⟨30,(6),[5,6],[150],232⟩,⟨30,(7),[1,2,5,6],[130],95⟩,⟨30,(7),[1,2,5,6],[146],157⟩,⟨30,(7),[1,5],[134],95⟩,⟨30,(7),[5],[135],183⟩,⟨30,(7),[5,6],[131],183⟩,⟨30,(7),[5,6],[150],232⟩,⟨30,(8),[1,2,5,6],[130],96⟩,⟨30,(8),[1,2,5,6],[146],158⟩,⟨30,(8),[1,5],[134],96⟩,⟨30,(8),[5],[135],184⟩,⟨30,(8),[5,6],[131],184⟩,⟨30,(8),[5,6],[150],233⟩,⟨30,(9),[1,2,5,6],[130],96⟩,⟨30,(9),[1,2,5,6],[146],158⟩,⟨30,(9),[1,5],[134],96⟩,⟨30,(9),[5],[135],184⟩,⟨30,(9),[5,6],[131],184⟩,⟨30,(9),[5,6],[150],233⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid832
  · exact recordValid_of_data section14Catalog 5 _ hnum valid833
  · exact recordValid_of_data section14Catalog 5 _ hnum valid834
  · exact recordValid_of_data section14Catalog 5 _ hnum valid835
  · exact recordValid_of_data section14Catalog 5 _ hnum valid836
  · exact recordValid_of_data section14Catalog 5 _ hnum valid837
  · exact recordValid_of_data section14Catalog 5 _ hnum valid838
  · exact recordValid_of_data section14Catalog 5 _ hnum valid839
  · exact recordValid_of_data section14Catalog 5 _ hnum valid840
  · exact recordValid_of_data section14Catalog 5 _ hnum valid841
  · exact recordValid_of_data section14Catalog 5 _ hnum valid842
  · exact recordValid_of_data section14Catalog 5 _ hnum valid843
  · exact recordValid_of_data section14Catalog 5 _ hnum valid844
  · exact recordValid_of_data section14Catalog 5 _ hnum valid845
  · exact recordValid_of_data section14Catalog 5 _ hnum valid846
  · exact recordValid_of_data section14Catalog 5 _ hnum valid847
  · exact recordValid_of_data section14Catalog 5 _ hnum valid848
  · exact recordValid_of_data section14Catalog 5 _ hnum valid849
  · exact recordValid_of_data section14Catalog 5 _ hnum valid850
  · exact recordValid_of_data section14Catalog 5 _ hnum valid851
  · exact recordValid_of_data section14Catalog 5 _ hnum valid852
  · exact recordValid_of_data section14Catalog 5 _ hnum valid853
  · exact recordValid_of_data section14Catalog 5 _ hnum valid854
  · exact recordValid_of_data section14Catalog 5 _ hnum valid855
  · exact recordValid_of_data section14Catalog 5 _ hnum valid856
  · exact recordValid_of_data section14Catalog 5 _ hnum valid857
  · exact recordValid_of_data section14Catalog 5 _ hnum valid858
  · exact recordValid_of_data section14Catalog 5 _ hnum valid859
  · exact recordValid_of_data section14Catalog 5 _ hnum valid860
  · exact recordValid_of_data section14Catalog 5 _ hnum valid861
  · exact recordValid_of_data section14Catalog 5 _ hnum valid862
  · exact recordValid_of_data section14Catalog 5 _ hnum valid863
end Section14Records_5_832_864

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_0832_0864


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_0864_0896
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_864_896
private theorem valid864 : RecordDataValid section14Catalog 5 (⟨33,(0),[1,2,5,6],[130],97⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨97,[1,2,5,6,9,10,13,14],97⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid865 : RecordDataValid section14Catalog 5 (⟨33,(0),[1,2,5,6,14],[131],97⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨97,[1,2,5,6,9,10,13,14],97⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid866 : RecordDataValid section14Catalog 5 (⟨33,(0),[1,5],[134,135],97⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨97,[1,2,5,6,9,10,13,14],97⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid867 : RecordDataValid section14Catalog 5 (⟨33,(0),[1,5,6],[146,150],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid868 : RecordDataValid section14Catalog 5 (⟨33,(1),[1,5],[134,135],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid869 : RecordDataValid section14Catalog 5 (⟨33,(1),[1,5,6],[130,131],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid870 : RecordDataValid section14Catalog 5 (⟨33,(1),[2,5,6,14],[146,150],159⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨159,[1,2,3,5,6,7,9,10,11,13,14,15],159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid871 : RecordDataValid section14Catalog 5 (⟨33,(2),[1,5],[130,131,134,135],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid872 : RecordDataValid section14Catalog 5 (⟨33,(2),[1,5,6,13,14],[146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid873 : RecordDataValid section14Catalog 5 (⟨33,(3),[1,5],[134],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid874 : RecordDataValid section14Catalog 5 (⟨33,(3),[1,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid875 : RecordDataValid section14Catalog 5 (⟨33,(3),[1,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid876 : RecordDataValid section14Catalog 5 (⟨33,(3),[1,5,13],[135],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid877 : RecordDataValid section14Catalog 5 (⟨33,(4),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid878 : RecordDataValid section14Catalog 5 (⟨33,(4),[1,2,5,6,13,14],[131],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid879 : RecordDataValid section14Catalog 5 (⟨33,(4),[1,5],[134],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid880 : RecordDataValid section14Catalog 5 (⟨33,(4),[1,5,6],[146,150],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid881 : RecordDataValid section14Catalog 5 (⟨33,(4),[1,5,13],[135],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid882 : RecordDataValid section14Catalog 5 (⟨33,(5),[1,2,5,6,13,14],[146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid883 : RecordDataValid section14Catalog 5 (⟨33,(5),[1,5],[134,135],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid884 : RecordDataValid section14Catalog 5 (⟨33,(5),[1,5,6],[130,131],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid885 : RecordDataValid section14Catalog 5 (⟨33,(6),[1,5],[134],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid886 : RecordDataValid section14Catalog 5 (⟨33,(6),[1,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid887 : RecordDataValid section14Catalog 5 (⟨33,(6),[1,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid888 : RecordDataValid section14Catalog 5 (⟨33,(6),[1,5,13],[135],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid889 : RecordDataValid section14Catalog 5 (⟨33,(7),[1,5],[134],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid890 : RecordDataValid section14Catalog 5 (⟨33,(7),[1,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid891 : RecordDataValid section14Catalog 5 (⟨33,(7),[1,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid892 : RecordDataValid section14Catalog 5 (⟨33,(7),[1,5,13],[135],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid893 : RecordDataValid section14Catalog 5 (⟨33,(8),[1,2,5,6],[130],97⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨97,[1,2,5,6,9,10,13,14],97⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid894 : RecordDataValid section14Catalog 5 (⟨33,(8),[1,2,5,6,13,14],[131],97⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨97,[1,2,5,6,9,10,13,14],97⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid895 : RecordDataValid section14Catalog 5 (⟨33,(8),[1,2,5,6,13,14],[146,150],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_0864_0896 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 864).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 864).take 32 = [⟨33,(0),[1,2,5,6],[130],97⟩,⟨33,(0),[1,2,5,6,14],[131],97⟩,⟨33,(0),[1,5],[134,135],97⟩,⟨33,(0),[1,5,6],[146,150],98⟩,⟨33,(1),[1,5],[134,135],98⟩,⟨33,(1),[1,5,6],[130,131],98⟩,⟨33,(1),[2,5,6,14],[146,150],159⟩,⟨33,(2),[1,5],[130,131,134,135],3⟩,⟨33,(2),[1,5,6,13,14],[146,150],3⟩,⟨33,(3),[1,5],[134],3⟩,⟨33,(3),[1,5,6],[130],3⟩,⟨33,(3),[1,5,6,13,14],[131,146,150],3⟩,⟨33,(3),[1,5,13],[135],3⟩,⟨33,(4),[1,2,5,6],[130],2⟩,⟨33,(4),[1,2,5,6,13,14],[131],2⟩,⟨33,(4),[1,5],[134],2⟩,⟨33,(4),[1,5,6],[146,150],98⟩,⟨33,(4),[1,5,13],[135],2⟩,⟨33,(5),[1,2,5,6,13,14],[146,150],2⟩,⟨33,(5),[1,5],[134,135],98⟩,⟨33,(5),[1,5,6],[130,131],98⟩,⟨33,(6),[1,5],[134],3⟩,⟨33,(6),[1,5,6],[130],3⟩,⟨33,(6),[1,5,6,13,14],[131,146,150],3⟩,⟨33,(6),[1,5,13],[135],3⟩,⟨33,(7),[1,5],[134],3⟩,⟨33,(7),[1,5,6],[130],3⟩,⟨33,(7),[1,5,6,13,14],[131,146,150],3⟩,⟨33,(7),[1,5,13],[135],3⟩,⟨33,(8),[1,2,5,6],[130],97⟩,⟨33,(8),[1,2,5,6,13,14],[131],97⟩,⟨33,(8),[1,2,5,6,13,14],[146,150],98⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid864
  · exact recordValid_of_data section14Catalog 5 _ hnum valid865
  · exact recordValid_of_data section14Catalog 5 _ hnum valid866
  · exact recordValid_of_data section14Catalog 5 _ hnum valid867
  · exact recordValid_of_data section14Catalog 5 _ hnum valid868
  · exact recordValid_of_data section14Catalog 5 _ hnum valid869
  · exact recordValid_of_data section14Catalog 5 _ hnum valid870
  · exact recordValid_of_data section14Catalog 5 _ hnum valid871
  · exact recordValid_of_data section14Catalog 5 _ hnum valid872
  · exact recordValid_of_data section14Catalog 5 _ hnum valid873
  · exact recordValid_of_data section14Catalog 5 _ hnum valid874
  · exact recordValid_of_data section14Catalog 5 _ hnum valid875
  · exact recordValid_of_data section14Catalog 5 _ hnum valid876
  · exact recordValid_of_data section14Catalog 5 _ hnum valid877
  · exact recordValid_of_data section14Catalog 5 _ hnum valid878
  · exact recordValid_of_data section14Catalog 5 _ hnum valid879
  · exact recordValid_of_data section14Catalog 5 _ hnum valid880
  · exact recordValid_of_data section14Catalog 5 _ hnum valid881
  · exact recordValid_of_data section14Catalog 5 _ hnum valid882
  · exact recordValid_of_data section14Catalog 5 _ hnum valid883
  · exact recordValid_of_data section14Catalog 5 _ hnum valid884
  · exact recordValid_of_data section14Catalog 5 _ hnum valid885
  · exact recordValid_of_data section14Catalog 5 _ hnum valid886
  · exact recordValid_of_data section14Catalog 5 _ hnum valid887
  · exact recordValid_of_data section14Catalog 5 _ hnum valid888
  · exact recordValid_of_data section14Catalog 5 _ hnum valid889
  · exact recordValid_of_data section14Catalog 5 _ hnum valid890
  · exact recordValid_of_data section14Catalog 5 _ hnum valid891
  · exact recordValid_of_data section14Catalog 5 _ hnum valid892
  · exact recordValid_of_data section14Catalog 5 _ hnum valid893
  · exact recordValid_of_data section14Catalog 5 _ hnum valid894
  · exact recordValid_of_data section14Catalog 5 _ hnum valid895
end Section14Records_5_864_896

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_0864_0896

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 768).take 128, section14RecordValid section14Catalog 5 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (5 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 5 r
  exact (all_of_interval_split P xs 768 832 896 (by decide) (by decide) (all_of_interval_split P xs 768 800 832 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_0768_0800 hnum) (Freiman.workReverse20260919_s0005_records_0800_0832 hnum)) (all_of_interval_split P xs 832 864 896 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_0832_0864 hnum) (Freiman.workReverse20260919_s0005_records_0864_0896 hnum)))

#print axioms solution
