-- Prove2me | solution 1 for Freiman.section14_s0008_records_1728_1760
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T07:37:22.164709+00:00
-- url     : https://prove2.me/submissions/0d0e1c02-fc2b-4973-86e4-2d8e8922c5ca

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
namespace Section14Records_8_1728_1760
private theorem valid1728 : RecordDataValid section14Catalog 8 (⟨230,(5),[3,4,7,8,12,15,16],[10],810⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨810,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],811⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1729 : RecordDataValid section14Catalog 8 (⟨230,(6),[3,4,7,8,15,16],[10],811⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨811,[1,2,3,4,5,6,7,8,9,10,11,13,14,15,16],812⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1730 : RecordDataValid section14Catalog 8 (⟨230,(7),[4,8,12,16],[10],815⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨815,[1,4,5,6,8,9,10,12,13,16],816⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1731 : RecordDataValid section14Catalog 8 (⟨230,(8),[3,4,7,8,12,15,16],[10],816⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨816,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],817⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1732 : RecordDataValid section14Catalog 8 (⟨230,(9),[4,8,12,16],[10],1375⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1375,[4,5,8,9,12,16],1379⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1733 : RecordDataValid section14Catalog 8 (⟨230,(10),[3,4,7,8,12,15,16],[10],818⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨818,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],819⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1734 : RecordDataValid section14Catalog 8 (⟨230,(11),[3,4,7,8,12,15,16],[10],819⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨819,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],820⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1735 : RecordDataValid section14Catalog 8 (⟨230,(12),[4,8,12,16],[10],820⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨820,[1,4,5,8,9,10,12,13,16],821⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1736 : RecordDataValid section14Catalog 8 (⟨230,(13),[3,4,7,8,12,15,16],[10],821⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨821,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],822⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1737 : RecordDataValid section14Catalog 8 (⟨230,(14),[4,8,12,16],[10],1375⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1375,[4,5,8,9,12,16],1379⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1738 : RecordDataValid section14Catalog 8 (⟨230,(15),[3,4,7,8,12,15,16],[10],822⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨822,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],823⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1739 : RecordDataValid section14Catalog 8 (⟨230,(16),[3,4,7,8,12,15,16],[10],823⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨823,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],824⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1740 : RecordDataValid section14Catalog 8 (⟨230,(17),[4,8,12,16],[10],1376⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1376,[4,8,9,12,16],1380⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1741 : RecordDataValid section14Catalog 8 (⟨230,(18),[3,4,7,8,12,15,16],[10],825⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨825,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],826⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1742 : RecordDataValid section14Catalog 8 (⟨230,(19),[4,8,12,16],[10],1376⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1376,[4,8,9,12,16],1380⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1743 : RecordDataValid section14Catalog 8 (⟨230,(20),[3,4,7,8,12,15,16],[10],826⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨826,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],827⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1744 : RecordDataValid section14Catalog 8 (⟨230,(21),[3,4,7,8,12,15,16],[10],827⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨827,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],828⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1745 : RecordDataValid section14Catalog 8 (⟨230,(22),[4,8,12,16],[10],1377⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1377,[4,8,9,12,16],1381⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1746 : RecordDataValid section14Catalog 8 (⟨230,(23),[3,4,7,8,12,15,16],[10],829⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨829,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],830⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1747 : RecordDataValid section14Catalog 8 (⟨230,(24),[4,8,12,16],[10],1377⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1377,[4,8,9,12,16],1381⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1748 : RecordDataValid section14Catalog 8 (⟨231,(0),[3,4,8,12,15,16],[10],830⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨830,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],831⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1749 : RecordDataValid section14Catalog 8 (⟨231,(1),[8,12],[10],1646⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1646,[8,9,12],1651⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1750 : RecordDataValid section14Catalog 8 (⟨231,(2),[3,4,7,8,12,15,16],[10],832⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨832,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],833⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1751 : RecordDataValid section14Catalog 8 (⟨231,(3),[3,4,7,8,12,15,16],[10],833⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨833,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],834⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1752 : RecordDataValid section14Catalog 8 (⟨231,(4),[3,4,8,12,15,16],[10],830⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨830,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],831⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1753 : RecordDataValid section14Catalog 8 (⟨231,(5),[8,12],[10],1646⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1646,[8,9,12],1651⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1754 : RecordDataValid section14Catalog 8 (⟨231,(6),[3,4,7,8,12,15,16],[10],832⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨832,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],833⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1755 : RecordDataValid section14Catalog 8 (⟨231,(7),[3,4,7,8,12,15,16],[10],833⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨833,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],834⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1756 : RecordDataValid section14Catalog 8 (⟨231,(8),[3,4,7,8,12,15,16],[10],834⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨834,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],835⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1757 : RecordDataValid section14Catalog 8 (⟨231,(9),[3,4,7,8,12,15,16],[10],835⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨835,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],836⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1758 : RecordDataValid section14Catalog 8 (⟨231,(10),[3,4,7,8,12,15,16],[10],836⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨836,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],837⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1759 : RecordDataValid section14Catalog 8 (⟨231,(11),[3,4,7,8,12,15,16],[10],837⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨837,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],838⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1728).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1728).take 32 = [⟨230,(5),[3,4,7,8,12,15,16],[10],810⟩,⟨230,(6),[3,4,7,8,15,16],[10],811⟩,⟨230,(7),[4,8,12,16],[10],815⟩,⟨230,(8),[3,4,7,8,12,15,16],[10],816⟩,⟨230,(9),[4,8,12,16],[10],1375⟩,⟨230,(10),[3,4,7,8,12,15,16],[10],818⟩,⟨230,(11),[3,4,7,8,12,15,16],[10],819⟩,⟨230,(12),[4,8,12,16],[10],820⟩,⟨230,(13),[3,4,7,8,12,15,16],[10],821⟩,⟨230,(14),[4,8,12,16],[10],1375⟩,⟨230,(15),[3,4,7,8,12,15,16],[10],822⟩,⟨230,(16),[3,4,7,8,12,15,16],[10],823⟩,⟨230,(17),[4,8,12,16],[10],1376⟩,⟨230,(18),[3,4,7,8,12,15,16],[10],825⟩,⟨230,(19),[4,8,12,16],[10],1376⟩,⟨230,(20),[3,4,7,8,12,15,16],[10],826⟩,⟨230,(21),[3,4,7,8,12,15,16],[10],827⟩,⟨230,(22),[4,8,12,16],[10],1377⟩,⟨230,(23),[3,4,7,8,12,15,16],[10],829⟩,⟨230,(24),[4,8,12,16],[10],1377⟩,⟨231,(0),[3,4,8,12,15,16],[10],830⟩,⟨231,(1),[8,12],[10],1646⟩,⟨231,(2),[3,4,7,8,12,15,16],[10],832⟩,⟨231,(3),[3,4,7,8,12,15,16],[10],833⟩,⟨231,(4),[3,4,8,12,15,16],[10],830⟩,⟨231,(5),[8,12],[10],1646⟩,⟨231,(6),[3,4,7,8,12,15,16],[10],832⟩,⟨231,(7),[3,4,7,8,12,15,16],[10],833⟩,⟨231,(8),[3,4,7,8,12,15,16],[10],834⟩,⟨231,(9),[3,4,7,8,12,15,16],[10],835⟩,⟨231,(10),[3,4,7,8,12,15,16],[10],836⟩,⟨231,(11),[3,4,7,8,12,15,16],[10],837⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1728
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1729
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1730
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1731
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1732
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1733
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1734
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1735
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1736
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1737
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1738
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1739
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1740
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1741
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1742
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1743
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1744
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1745
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1746
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1747
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1748
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1749
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1750
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1751
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1752
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1753
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1754
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1755
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1756
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1757
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1758
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1759
end Section14Records_8_1728_1760

#print axioms solution
