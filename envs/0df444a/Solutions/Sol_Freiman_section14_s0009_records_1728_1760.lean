-- Prove2me | solution 1 for Freiman.section14_s0009_records_1728_1760
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T20:56:36.042514+00:00
-- url     : https://prove2.me/submissions/ae22277f-b3d4-4de2-a743-685895faae23

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
namespace Section14Records_9_1728_1760
private theorem valid1728 : RecordDataValid section14Catalog 9 (⟨185,(5),[9,10],[42],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1729 : RecordDataValid section14Catalog 9 (⟨185,(6),[9,10],[42],682⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨682,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],683⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1730 : RecordDataValid section14Catalog 9 (⟨185,(7),[9,10],[42],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1731 : RecordDataValid section14Catalog 9 (⟨185,(8),[9,10],[42],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1732 : RecordDataValid section14Catalog 9 (⟨185,(9),[9,10],[42],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1733 : RecordDataValid section14Catalog 9 (⟨185,(10),[9,10],[42],680⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨680,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],681⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1734 : RecordDataValid section14Catalog 9 (⟨185,(11),[9,10],[42],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1735 : RecordDataValid section14Catalog 9 (⟨185,(12),[9,10],[42],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1736 : RecordDataValid section14Catalog 9 (⟨185,(13),[9,10],[42],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1737 : RecordDataValid section14Catalog 9 (⟨185,(14),[9,10],[42],683⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨683,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],684⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1738 : RecordDataValid section14Catalog 9 (⟨185,(15),[9,10],[42],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1739 : RecordDataValid section14Catalog 9 (⟨188,(0),[9],[42],1309⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1309,[4,8,9,12,16],1313⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1740 : RecordDataValid section14Catalog 9 (⟨188,(1),[9],[42],1310⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1310,[4,8,9,12,16],1314⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1741 : RecordDataValid section14Catalog 9 (⟨188,(2),[9],[42],1309⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1309,[4,8,9,12,16],1313⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1742 : RecordDataValid section14Catalog 9 (⟨188,(3),[9],[42],1311⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1311,[4,8,9,12,16],1315⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1743 : RecordDataValid section14Catalog 9 (⟨188,(4),[9],[42],1312⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1312,[4,8,9,12,16],1316⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1744 : RecordDataValid section14Catalog 9 (⟨188,(5),[9],[42],1312⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1312,[4,8,9,12,16],1316⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1745 : RecordDataValid section14Catalog 9 (⟨188,(6),[9],[42],1312⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1312,[4,8,9,12,16],1316⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1746 : RecordDataValid section14Catalog 9 (⟨188,(7),[9],[42],1312⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1312,[4,8,9,12,16],1316⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1747 : RecordDataValid section14Catalog 9 (⟨188,(8),[9],[42],1313⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1313,[4,8,9,12,16],1317⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1748 : RecordDataValid section14Catalog 9 (⟨188,(9),[9],[42],1313⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1313,[4,8,9,12,16],1317⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1749 : RecordDataValid section14Catalog 9 (⟨188,(10),[9],[42],1313⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1313,[4,8,9,12,16],1317⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1750 : RecordDataValid section14Catalog 9 (⟨188,(11),[9],[42],1313⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1313,[4,8,9,12,16],1317⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1751 : RecordDataValid section14Catalog 9 (⟨188,(12),[9],[42],1314⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1314,[4,8,9,12,16],1318⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1752 : RecordDataValid section14Catalog 9 (⟨188,(13),[9],[42],1314⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1314,[4,8,9,12,16],1318⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1753 : RecordDataValid section14Catalog 9 (⟨188,(14),[9],[42],1314⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1314,[4,8,9,12,16],1318⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1754 : RecordDataValid section14Catalog 9 (⟨188,(15),[9],[42],1314⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1314,[4,8,9,12,16],1318⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1755 : RecordDataValid section14Catalog 9 (⟨190,(0),[9,10],[42],690⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨690,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],691⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1756 : RecordDataValid section14Catalog 9 (⟨190,(1),[9,10],[42],690⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨690,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],691⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1757 : RecordDataValid section14Catalog 9 (⟨190,(2),[9,10],[42],690⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨690,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],691⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1758 : RecordDataValid section14Catalog 9 (⟨190,(3),[9,10],[42],690⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨690,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],691⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1759 : RecordDataValid section14Catalog 9 (⟨190,(4),[9,10],[42],690⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨690,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],691⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 1728).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 1728).take 32 = [⟨185,(5),[9,10],[42],679⟩,⟨185,(6),[9,10],[42],682⟩,⟨185,(7),[9,10],[42],681⟩,⟨185,(8),[9,10],[42],678⟩,⟨185,(9),[9,10],[42],679⟩,⟨185,(10),[9,10],[42],680⟩,⟨185,(11),[9,10],[42],681⟩,⟨185,(12),[9,10],[42],678⟩,⟨185,(13),[9,10],[42],679⟩,⟨185,(14),[9,10],[42],683⟩,⟨185,(15),[9,10],[42],681⟩,⟨188,(0),[9],[42],1309⟩,⟨188,(1),[9],[42],1310⟩,⟨188,(2),[9],[42],1309⟩,⟨188,(3),[9],[42],1311⟩,⟨188,(4),[9],[42],1312⟩,⟨188,(5),[9],[42],1312⟩,⟨188,(6),[9],[42],1312⟩,⟨188,(7),[9],[42],1312⟩,⟨188,(8),[9],[42],1313⟩,⟨188,(9),[9],[42],1313⟩,⟨188,(10),[9],[42],1313⟩,⟨188,(11),[9],[42],1313⟩,⟨188,(12),[9],[42],1314⟩,⟨188,(13),[9],[42],1314⟩,⟨188,(14),[9],[42],1314⟩,⟨188,(15),[9],[42],1314⟩,⟨190,(0),[9,10],[42],690⟩,⟨190,(1),[9,10],[42],690⟩,⟨190,(2),[9,10],[42],690⟩,⟨190,(3),[9,10],[42],690⟩,⟨190,(4),[9,10],[42],690⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1728
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1729
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1730
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1731
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1732
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1733
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1734
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1735
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1736
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1737
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1738
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1739
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1740
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1741
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1742
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1743
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1744
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1745
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1746
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1747
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1748
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1749
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1750
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1751
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1752
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1753
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1754
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1755
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1756
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1757
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1758
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1759
end Section14Records_9_1728_1760

#print axioms solution
