-- Prove2me | solution 1 for Freiman.section14_s0009_records_2784_2816
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T21:46:34.387894+00:00
-- url     : https://prove2.me/submissions/7b43957e-cb26-4963-94e8-013c96a39c71

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
namespace Section14Records_9_2784_2816
private theorem valid2784 : RecordDataValid section14Catalog 9 (⟨317,(8),[9],[42],1492⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1492,[5,8,9,12],1497⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2785 : RecordDataValid section14Catalog 9 (⟨317,(9),[9],[42],1493⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1493,[5,8,9,12],1498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2786 : RecordDataValid section14Catalog 9 (⟨317,(10),[9],[42],1494⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1494,[5,8,9,12],1499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2787 : RecordDataValid section14Catalog 9 (⟨317,(11),[9],[42],1495⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1495,[5,8,9,12],1500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2788 : RecordDataValid section14Catalog 9 (⟨317,(12),[9],[42],1496⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1496,[5,8,9,12],1501⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2789 : RecordDataValid section14Catalog 9 (⟨317,(13),[9],[42],1493⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1493,[5,8,9,12],1498⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2790 : RecordDataValid section14Catalog 9 (⟨317,(14),[9],[42],1494⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1494,[5,8,9,12],1499⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2791 : RecordDataValid section14Catalog 9 (⟨317,(15),[9],[42],1495⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1495,[5,8,9,12],1500⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2792 : RecordDataValid section14Catalog 9 (⟨318,(0),[9],[42],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2793 : RecordDataValid section14Catalog 9 (⟨318,(1),[9],[42],1497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1497,[5,8,9,12],1502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2794 : RecordDataValid section14Catalog 9 (⟨318,(2),[9],[42],1498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1498,[5,8,9,12],1503⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2795 : RecordDataValid section14Catalog 9 (⟨318,(3),[9],[42],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2796 : RecordDataValid section14Catalog 9 (⟨318,(4),[9],[42],1498⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1498,[5,8,9,12],1503⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2797 : RecordDataValid section14Catalog 9 (⟨318,(5),[9],[42],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2798 : RecordDataValid section14Catalog 9 (⟨318,(6),[9],[42],1497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1497,[5,8,9,12],1502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2799 : RecordDataValid section14Catalog 9 (⟨318,(7),[9],[42],1499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1499,[5,8,9,12],1504⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2800 : RecordDataValid section14Catalog 9 (⟨318,(8),[9],[42],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2801 : RecordDataValid section14Catalog 9 (⟨318,(9),[9],[42],1499⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1499,[5,8,9,12],1504⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2802 : RecordDataValid section14Catalog 9 (⟨318,(10),[9],[42],1500⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1500,[5,8,9,12],1505⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2803 : RecordDataValid section14Catalog 9 (⟨318,(11),[9],[42],1501⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1501,[5,8,9,12],1506⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2804 : RecordDataValid section14Catalog 9 (⟨318,(12),[9],[42],1502⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1502,[5,8,9,12],1507⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2805 : RecordDataValid section14Catalog 9 (⟨318,(13),[9],[42],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2806 : RecordDataValid section14Catalog 9 (⟨318,(14),[9],[42],1502⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1502,[5,8,9,12],1507⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2807 : RecordDataValid section14Catalog 9 (⟨318,(15),[9],[42],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2808 : RecordDataValid section14Catalog 9 (⟨318,(16),[9],[42],1497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1497,[5,8,9,12],1502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2809 : RecordDataValid section14Catalog 9 (⟨318,(17),[9],[42],1503⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1503,[5,8,9,12],1508⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2810 : RecordDataValid section14Catalog 9 (⟨318,(18),[9],[42],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2811 : RecordDataValid section14Catalog 9 (⟨318,(19),[9],[42],1503⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1503,[5,8,9,12],1508⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2812 : RecordDataValid section14Catalog 9 (⟨319,(0),[9],[42],1231⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1231,[3,5,7,8,9,11,12,15],1235⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2813 : RecordDataValid section14Catalog 9 (⟨319,(1),[9],[42],1229⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1229,[3,5,7,8,9,11,12,15],1233⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2814 : RecordDataValid section14Catalog 9 (⟨319,(2),[9],[42],1228⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1228,[3,5,7,8,9,11,12,15],1232⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2815 : RecordDataValid section14Catalog 9 (⟨319,(3),[9],[42],1230⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1230,[3,5,7,8,9,11,12,15],1234⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2784).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2784).take 32 = [⟨317,(8),[9],[42],1492⟩,⟨317,(9),[9],[42],1493⟩,⟨317,(10),[9],[42],1494⟩,⟨317,(11),[9],[42],1495⟩,⟨317,(12),[9],[42],1496⟩,⟨317,(13),[9],[42],1493⟩,⟨317,(14),[9],[42],1494⟩,⟨317,(15),[9],[42],1495⟩,⟨318,(0),[9],[42],882⟩,⟨318,(1),[9],[42],1497⟩,⟨318,(2),[9],[42],1498⟩,⟨318,(3),[9],[42],101⟩,⟨318,(4),[9],[42],1498⟩,⟨318,(5),[9],[42],882⟩,⟨318,(6),[9],[42],1497⟩,⟨318,(7),[9],[42],1499⟩,⟨318,(8),[9],[42],101⟩,⟨318,(9),[9],[42],1499⟩,⟨318,(10),[9],[42],1500⟩,⟨318,(11),[9],[42],1501⟩,⟨318,(12),[9],[42],1502⟩,⟨318,(13),[9],[42],101⟩,⟨318,(14),[9],[42],1502⟩,⟨318,(15),[9],[42],882⟩,⟨318,(16),[9],[42],1497⟩,⟨318,(17),[9],[42],1503⟩,⟨318,(18),[9],[42],101⟩,⟨318,(19),[9],[42],1503⟩,⟨319,(0),[9],[42],1231⟩,⟨319,(1),[9],[42],1229⟩,⟨319,(2),[9],[42],1228⟩,⟨319,(3),[9],[42],1230⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2784
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2785
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2786
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2787
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2788
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2789
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2790
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2791
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2792
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2793
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2794
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2795
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2796
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2797
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2798
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2799
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2800
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2801
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2802
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2803
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2804
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2805
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2806
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2807
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2808
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2809
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2810
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2811
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2812
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2813
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2814
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2815
end Section14Records_9_2784_2816

#print axioms solution
