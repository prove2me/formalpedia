-- Prove2me | solution 1 for Freiman.section14_s0002_records_0768_0800
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T06:07:17.644397+00:00
-- url     : https://prove2.me/submissions/b7b19cb3-92e7-420a-9cca-748e5bf379d3

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
namespace Section14Records_2_768_800
private theorem valid768 : RecordDataValid section14Catalog 2 (⟨30,(1),[1,2],[147],181⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨181,[1,2,5,6,9,10],181⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid769 : RecordDataValid section14Catalog 2 (⟨30,(1),[1,2,5,6],[146,150],153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨153,[1,2,3,4,5,6,7,8,9,10,11,12],153⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid770 : RecordDataValid section14Catalog 2 (⟨30,(2),[1,2],[147],120⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨120,[1,2,5,6,9,10],120⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid771 : RecordDataValid section14Catalog 2 (⟨30,(2),[1,2],[190],200⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨200,[1,2,3,4,5,6,7,8,9,10,11,12],200⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid772 : RecordDataValid section14Catalog 2 (⟨30,(2),[1,2,5,6],[130],92⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨92,[1,2,5,6,9,10,12],92⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid773 : RecordDataValid section14Catalog 2 (⟨30,(2),[1,2,5,6],[146],154⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨154,[1,2,3,5,6,7],154⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid774 : RecordDataValid section14Catalog 2 (⟨30,(2),[1,2,5,6],[150],200⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨200,[1,2,3,4,5,6,7,8,9,10,11,12],200⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid775 : RecordDataValid section14Catalog 2 (⟨30,(2),[2],[131],92⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨92,[1,2,5,6,9,10,12],92⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid776 : RecordDataValid section14Catalog 2 (⟨30,(3),[1,2],[131],93⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨93,[1,2,5,6,9,10,12],93⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid777 : RecordDataValid section14Catalog 2 (⟨30,(3),[1,2],[147],181⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨181,[1,2,5,6,9,10],181⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid778 : RecordDataValid section14Catalog 2 (⟨30,(3),[1,2],[150],201⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨201,[1,2,3,4],201⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid779 : RecordDataValid section14Catalog 2 (⟨30,(3),[1,2],[190],230⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨230,[1,2,3,4,5,6,7,8,9,10,11,12],230⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid780 : RecordDataValid section14Catalog 2 (⟨30,(3),[1,2,5,6],[130],93⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨93,[1,2,5,6,9,10,12],93⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid781 : RecordDataValid section14Catalog 2 (⟨30,(3),[1,2,5,6],[146],155⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨155,[1,2,3,5,6,7],155⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid782 : RecordDataValid section14Catalog 2 (⟨30,(4),[1,2],[131],94⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨94,[1,2,5,6,9,10,12],94⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid783 : RecordDataValid section14Catalog 2 (⟨30,(4),[1,2],[147],182⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨182,[1,2,5,6,9,10],182⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid784 : RecordDataValid section14Catalog 2 (⟨30,(4),[1,2],[150],202⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨202,[1,2,3,4],202⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid785 : RecordDataValid section14Catalog 2 (⟨30,(4),[1,2],[190],231⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨231,[1,2,3,4,5,6,7,8,9,10,11,12],231⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid786 : RecordDataValid section14Catalog 2 (⟨30,(4),[1,2,5,6],[130],94⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨94,[1,2,5,6,9,10,12],94⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid787 : RecordDataValid section14Catalog 2 (⟨30,(4),[1,2,5,6],[146],156⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨156,[1,2,3,5,6,7],156⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid788 : RecordDataValid section14Catalog 2 (⟨30,(5),[1,2],[131],93⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨93,[1,2,5,6,9,10,12],93⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid789 : RecordDataValid section14Catalog 2 (⟨30,(5),[1,2],[147],181⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨181,[1,2,5,6,9,10],181⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid790 : RecordDataValid section14Catalog 2 (⟨30,(5),[1,2],[150],201⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨201,[1,2,3,4],201⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid791 : RecordDataValid section14Catalog 2 (⟨30,(5),[1,2],[190],230⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨230,[1,2,3,4,5,6,7,8,9,10,11,12],230⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid792 : RecordDataValid section14Catalog 2 (⟨30,(5),[1,2,5,6],[130],93⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨93,[1,2,5,6,9,10,12],93⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid793 : RecordDataValid section14Catalog 2 (⟨30,(5),[1,2,5,6],[146],155⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨155,[1,2,3,5,6,7],155⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid794 : RecordDataValid section14Catalog 2 (⟨30,(6),[1,2],[131],95⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨95,[1,2,5,6,9,10,12],95⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid795 : RecordDataValid section14Catalog 2 (⟨30,(6),[1,2],[147],183⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨183,[1,2,5,6,9,10],183⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid796 : RecordDataValid section14Catalog 2 (⟨30,(6),[1,2],[150],203⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨203,[1,2,3,4],203⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid797 : RecordDataValid section14Catalog 2 (⟨30,(6),[1,2],[190],232⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨232,[1,2,3,4,5,6,7,8,9,10,11,12],232⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid798 : RecordDataValid section14Catalog 2 (⟨30,(6),[1,2,5,6],[130],95⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨95,[1,2,5,6,9,10,12],95⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid799 : RecordDataValid section14Catalog 2 (⟨30,(6),[1,2,5,6],[146],157⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨157,[1,2,3,5,6,7],157⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 768).take 32, section14RecordValid section14Catalog 2 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 768).take 32 = [⟨30,(1),[1,2],[147],181⟩,⟨30,(1),[1,2,5,6],[146,150],153⟩,⟨30,(2),[1,2],[147],120⟩,⟨30,(2),[1,2],[190],200⟩,⟨30,(2),[1,2,5,6],[130],92⟩,⟨30,(2),[1,2,5,6],[146],154⟩,⟨30,(2),[1,2,5,6],[150],200⟩,⟨30,(2),[2],[131],92⟩,⟨30,(3),[1,2],[131],93⟩,⟨30,(3),[1,2],[147],181⟩,⟨30,(3),[1,2],[150],201⟩,⟨30,(3),[1,2],[190],230⟩,⟨30,(3),[1,2,5,6],[130],93⟩,⟨30,(3),[1,2,5,6],[146],155⟩,⟨30,(4),[1,2],[131],94⟩,⟨30,(4),[1,2],[147],182⟩,⟨30,(4),[1,2],[150],202⟩,⟨30,(4),[1,2],[190],231⟩,⟨30,(4),[1,2,5,6],[130],94⟩,⟨30,(4),[1,2,5,6],[146],156⟩,⟨30,(5),[1,2],[131],93⟩,⟨30,(5),[1,2],[147],181⟩,⟨30,(5),[1,2],[150],201⟩,⟨30,(5),[1,2],[190],230⟩,⟨30,(5),[1,2,5,6],[130],93⟩,⟨30,(5),[1,2,5,6],[146],155⟩,⟨30,(6),[1,2],[131],95⟩,⟨30,(6),[1,2],[147],183⟩,⟨30,(6),[1,2],[150],203⟩,⟨30,(6),[1,2],[190],232⟩,⟨30,(6),[1,2,5,6],[130],95⟩,⟨30,(6),[1,2,5,6],[146],157⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 2 _ hnum valid768
  · exact recordValid_of_data section14Catalog 2 _ hnum valid769
  · exact recordValid_of_data section14Catalog 2 _ hnum valid770
  · exact recordValid_of_data section14Catalog 2 _ hnum valid771
  · exact recordValid_of_data section14Catalog 2 _ hnum valid772
  · exact recordValid_of_data section14Catalog 2 _ hnum valid773
  · exact recordValid_of_data section14Catalog 2 _ hnum valid774
  · exact recordValid_of_data section14Catalog 2 _ hnum valid775
  · exact recordValid_of_data section14Catalog 2 _ hnum valid776
  · exact recordValid_of_data section14Catalog 2 _ hnum valid777
  · exact recordValid_of_data section14Catalog 2 _ hnum valid778
  · exact recordValid_of_data section14Catalog 2 _ hnum valid779
  · exact recordValid_of_data section14Catalog 2 _ hnum valid780
  · exact recordValid_of_data section14Catalog 2 _ hnum valid781
  · exact recordValid_of_data section14Catalog 2 _ hnum valid782
  · exact recordValid_of_data section14Catalog 2 _ hnum valid783
  · exact recordValid_of_data section14Catalog 2 _ hnum valid784
  · exact recordValid_of_data section14Catalog 2 _ hnum valid785
  · exact recordValid_of_data section14Catalog 2 _ hnum valid786
  · exact recordValid_of_data section14Catalog 2 _ hnum valid787
  · exact recordValid_of_data section14Catalog 2 _ hnum valid788
  · exact recordValid_of_data section14Catalog 2 _ hnum valid789
  · exact recordValid_of_data section14Catalog 2 _ hnum valid790
  · exact recordValid_of_data section14Catalog 2 _ hnum valid791
  · exact recordValid_of_data section14Catalog 2 _ hnum valid792
  · exact recordValid_of_data section14Catalog 2 _ hnum valid793
  · exact recordValid_of_data section14Catalog 2 _ hnum valid794
  · exact recordValid_of_data section14Catalog 2 _ hnum valid795
  · exact recordValid_of_data section14Catalog 2 _ hnum valid796
  · exact recordValid_of_data section14Catalog 2 _ hnum valid797
  · exact recordValid_of_data section14Catalog 2 _ hnum valid798
  · exact recordValid_of_data section14Catalog 2 _ hnum valid799
end Section14Records_2_768_800

#print axioms solution
