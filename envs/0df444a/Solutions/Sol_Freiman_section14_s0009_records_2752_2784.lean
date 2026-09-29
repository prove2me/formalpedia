-- Prove2me | solution 1 for Freiman.section14_s0009_records_2752_2784
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T21:46:44.835327+00:00
-- url     : https://prove2.me/submissions/176400fe-9692-4391-96f4-5691df3398f2

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
namespace Section14Records_9_2752_2784
private theorem valid2752 : RecordDataValid section14Catalog 9 (⟨312,(0),[9],[42],1482⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1482,[5,8,9,12],1487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2753 : RecordDataValid section14Catalog 9 (⟨312,(1),[9],[42],1483⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1483,[5,8,9,12],1488⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2754 : RecordDataValid section14Catalog 9 (⟨312,(2),[9],[42],1482⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1482,[5,8,9,12],1487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2755 : RecordDataValid section14Catalog 9 (⟨312,(3),[9],[42],1484⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1484,[5,8,9,12],1489⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2756 : RecordDataValid section14Catalog 9 (⟨313,(0),[9],[42],1200⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1200,[3,5,7,8,9,11,12,15],1204⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2757 : RecordDataValid section14Catalog 9 (⟨313,(1),[9],[42],1201⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1201,[3,5,7,8,9,11,12,15],1205⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2758 : RecordDataValid section14Catalog 9 (⟨313,(2),[9],[42],1202⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1202,[3,5,7,8,9,11,12,15],1206⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2759 : RecordDataValid section14Catalog 9 (⟨313,(3),[9],[42],1203⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1203,[3,5,7,8,9,11,15],1207⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2760 : RecordDataValid section14Catalog 9 (⟨315,(0),[9],[42],1485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1485,[5,8,9,12],1490⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2761 : RecordDataValid section14Catalog 9 (⟨315,(1),[9],[42],1486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1486,[5,8,9,12],1491⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2762 : RecordDataValid section14Catalog 9 (⟨315,(2),[9],[42],1487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1487,[5,8,9,12],1492⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2763 : RecordDataValid section14Catalog 9 (⟨315,(3),[9],[42],1488⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1488,[5,8,9,12],1493⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2764 : RecordDataValid section14Catalog 9 (⟨315,(4),[9],[42],1489⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1489,[5,8,9,12],1494⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2765 : RecordDataValid section14Catalog 9 (⟨315,(5),[9],[42],1486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1486,[5,8,9,12],1491⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2766 : RecordDataValid section14Catalog 9 (⟨315,(6),[9],[42],1487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1487,[5,8,9,12],1492⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2767 : RecordDataValid section14Catalog 9 (⟨315,(7),[9],[42],1488⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1488,[5,8,9,12],1493⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2768 : RecordDataValid section14Catalog 9 (⟨315,(8),[9],[42],1485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1485,[5,8,9,12],1490⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2769 : RecordDataValid section14Catalog 9 (⟨315,(9),[9],[42],1490⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1490,[5,8,9,12],1495⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2770 : RecordDataValid section14Catalog 9 (⟨315,(10),[9],[42],1487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1487,[5,8,9,12],1492⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2771 : RecordDataValid section14Catalog 9 (⟨315,(11),[9],[42],1488⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1488,[5,8,9,12],1493⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2772 : RecordDataValid section14Catalog 9 (⟨315,(12),[9],[42],1491⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1491,[5,8,9,12],1496⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2773 : RecordDataValid section14Catalog 9 (⟨315,(13),[9],[42],1486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1486,[5,8,9,12],1491⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2774 : RecordDataValid section14Catalog 9 (⟨315,(14),[9],[42],1487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1487,[5,8,9,12],1492⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2775 : RecordDataValid section14Catalog 9 (⟨315,(15),[9],[42],1488⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1488,[5,8,9,12],1493⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2776 : RecordDataValid section14Catalog 9 (⟨317,(0),[9],[42],1211⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1211,[3,5,7,8,9,11,12,15],1215⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2777 : RecordDataValid section14Catalog 9 (⟨317,(1),[9],[42],1212⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1212,[3,5,7,8,9,11,12,15],1216⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2778 : RecordDataValid section14Catalog 9 (⟨317,(2),[9],[42],1213⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1213,[3,5,7,8,9,11,12,15],1217⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2779 : RecordDataValid section14Catalog 9 (⟨317,(3),[9],[42],1214⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1214,[3,5,7,8,9,11,12,15],1218⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2780 : RecordDataValid section14Catalog 9 (⟨317,(4),[9],[42],1215⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1215,[3,5,7,8,9,11,12,15],1219⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2781 : RecordDataValid section14Catalog 9 (⟨317,(5),[9],[42],1216⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1216,[3,5,7,8,9,11,12,15],1220⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2782 : RecordDataValid section14Catalog 9 (⟨317,(6),[9],[42],1217⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1217,[3,5,7,8,9,11,12,15],1221⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2783 : RecordDataValid section14Catalog 9 (⟨317,(7),[9],[42],1218⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1218,[3,5,7,8,9,11,12,15],1222⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2752).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2752).take 32 = [⟨312,(0),[9],[42],1482⟩,⟨312,(1),[9],[42],1483⟩,⟨312,(2),[9],[42],1482⟩,⟨312,(3),[9],[42],1484⟩,⟨313,(0),[9],[42],1200⟩,⟨313,(1),[9],[42],1201⟩,⟨313,(2),[9],[42],1202⟩,⟨313,(3),[9],[42],1203⟩,⟨315,(0),[9],[42],1485⟩,⟨315,(1),[9],[42],1486⟩,⟨315,(2),[9],[42],1487⟩,⟨315,(3),[9],[42],1488⟩,⟨315,(4),[9],[42],1489⟩,⟨315,(5),[9],[42],1486⟩,⟨315,(6),[9],[42],1487⟩,⟨315,(7),[9],[42],1488⟩,⟨315,(8),[9],[42],1485⟩,⟨315,(9),[9],[42],1490⟩,⟨315,(10),[9],[42],1487⟩,⟨315,(11),[9],[42],1488⟩,⟨315,(12),[9],[42],1491⟩,⟨315,(13),[9],[42],1486⟩,⟨315,(14),[9],[42],1487⟩,⟨315,(15),[9],[42],1488⟩,⟨317,(0),[9],[42],1211⟩,⟨317,(1),[9],[42],1212⟩,⟨317,(2),[9],[42],1213⟩,⟨317,(3),[9],[42],1214⟩,⟨317,(4),[9],[42],1215⟩,⟨317,(5),[9],[42],1216⟩,⟨317,(6),[9],[42],1217⟩,⟨317,(7),[9],[42],1218⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2752
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2753
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2754
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2755
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2756
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2757
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2758
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2759
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2760
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2761
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2762
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2763
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2764
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2765
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2766
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2767
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2768
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2769
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2770
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2771
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2772
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2773
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2774
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2775
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2776
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2777
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2778
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2779
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2780
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2781
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2782
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2783
end Section14Records_9_2752_2784

#print axioms solution
