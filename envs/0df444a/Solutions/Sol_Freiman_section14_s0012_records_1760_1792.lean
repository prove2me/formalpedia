-- Prove2me | solution 1 for Freiman.section14_s0012_records_1760_1792
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T05:09:53.625981+00:00
-- url     : https://prove2.me/submissions/4db8dbeb-a3c9-4b05-aa6b-11fbf94771e2

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
namespace Section14Records_12_1760_1792
private theorem valid1760 : RecordDataValid section14Catalog 12 (⟨253,(0),[12],[10],1718⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1718,[12],1723⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1761 : RecordDataValid section14Catalog 12 (⟨253,(1),[12],[10],1721⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1721,[12],1726⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1762 : RecordDataValid section14Catalog 12 (⟨253,(2),[12],[10],1722⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1722,[12],1727⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1763 : RecordDataValid section14Catalog 12 (⟨253,(3),[4,8,12,16],[10],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1764 : RecordDataValid section14Catalog 12 (⟨253,(4),[4,8,12,16],[10],30⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨30,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],30⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1765 : RecordDataValid section14Catalog 12 (⟨253,(5),[12],[10],1718⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1718,[12],1723⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1766 : RecordDataValid section14Catalog 12 (⟨253,(6),[12],[10],1721⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1721,[12],1726⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1767 : RecordDataValid section14Catalog 12 (⟨253,(7),[8,12],[10],1647⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1647,[8,9,12],1652⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1768 : RecordDataValid section14Catalog 12 (⟨253,(8),[4,8,12,16],[10],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1769 : RecordDataValid section14Catalog 12 (⟨253,(9),[4,8,12,16],[10],32⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨32,[1,2,4,5,6,8,9,10,12,13,14,16],32⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1770 : RecordDataValid section14Catalog 12 (⟨253,(10),[4,8,12,16],[10],84⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1771 : RecordDataValid section14Catalog 12 (⟨253,(11),[4,8,12,16],[10],897⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨897,[1,2,4,5,6,8,9,10,12,13,14,16],899⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1772 : RecordDataValid section14Catalog 12 (⟨253,(12),[4,8,12,16],[10],898⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨898,[1,2,4,5,6,8,9,10,12,13,14,16],900⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1773 : RecordDataValid section14Catalog 12 (⟨253,(13),[4,8,12,16],[10],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1774 : RecordDataValid section14Catalog 12 (⟨253,(14),[4,8,12,16],[10],34⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨34,[1,2,4,5,6,8,9,10,12,13,14,16],34⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1775 : RecordDataValid section14Catalog 12 (⟨253,(15),[4,8,12,16],[10],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1776 : RecordDataValid section14Catalog 12 (⟨253,(16),[4,8,12,16],[10],36⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨36,[1,2,4,5,6,8,9,10,12,13,14,16],36⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1777 : RecordDataValid section14Catalog 12 (⟨253,(17),[4,8,12,16],[10],37⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨37,[1,2,4,5,6,8,9,10,12,13,14,16],37⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1778 : RecordDataValid section14Catalog 12 (⟨253,(18),[4,8,12,16],[10],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1779 : RecordDataValid section14Catalog 12 (⟨253,(19),[4,8,12,16],[10],37⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨37,[1,2,4,5,6,8,9,10,12,13,14,16],37⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1780 : RecordDataValid section14Catalog 12 (⟨253,(20),[4,8,12,16],[10],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1781 : RecordDataValid section14Catalog 12 (⟨253,(21),[4,8,12,16],[10],39⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨39,[1,2,4,5,6,8,9,10,12,13,14,16],39⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1782 : RecordDataValid section14Catalog 12 (⟨253,(22),[4,8,12,16],[10],40⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨40,[1,2,4,5,6,8,9,10,12,13,14,16],40⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1783 : RecordDataValid section14Catalog 12 (⟨253,(23),[4,8,12,16],[10],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1784 : RecordDataValid section14Catalog 12 (⟨253,(24),[4,8,12,16],[10],40⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨40,[1,2,4,5,6,8,9,10,12,13,14,16],40⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1785 : RecordDataValid section14Catalog 12 (⟨259,(1),[4,8,12],[10],906⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨906,[1,2,4,5,6,8,9,10,12],908⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1786 : RecordDataValid section14Catalog 12 (⟨259,(3),[4,8,12],[10],907⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨907,[1,2,4,5,6,8,9,10,12],909⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1787 : RecordDataValid section14Catalog 12 (⟨259,(5),[8,12],[10],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1788 : RecordDataValid section14Catalog 12 (⟨259,(7),[8,12],[10],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1789 : RecordDataValid section14Catalog 12 (⟨259,(11),[4,12],[10],52⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨52,[1,2,4,9,12],52⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1790 : RecordDataValid section14Catalog 12 (⟨259,(13),[8,12],[10],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1791 : RecordDataValid section14Catalog 12 (⟨259,(15),[12],[10],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1760).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1760).take 32 = [⟨253,(0),[12],[10],1718⟩,⟨253,(1),[12],[10],1721⟩,⟨253,(2),[12],[10],1722⟩,⟨253,(3),[4,8,12,16],[10],29⟩,⟨253,(4),[4,8,12,16],[10],30⟩,⟨253,(5),[12],[10],1718⟩,⟨253,(6),[12],[10],1721⟩,⟨253,(7),[8,12],[10],1647⟩,⟨253,(8),[4,8,12,16],[10],29⟩,⟨253,(9),[4,8,12,16],[10],32⟩,⟨253,(10),[4,8,12,16],[10],84⟩,⟨253,(11),[4,8,12,16],[10],897⟩,⟨253,(12),[4,8,12,16],[10],898⟩,⟨253,(13),[4,8,12,16],[10],29⟩,⟨253,(14),[4,8,12,16],[10],34⟩,⟨253,(15),[4,8,12,16],[10],35⟩,⟨253,(16),[4,8,12,16],[10],36⟩,⟨253,(17),[4,8,12,16],[10],37⟩,⟨253,(18),[4,8,12,16],[10],29⟩,⟨253,(19),[4,8,12,16],[10],37⟩,⟨253,(20),[4,8,12,16],[10],38⟩,⟨253,(21),[4,8,12,16],[10],39⟩,⟨253,(22),[4,8,12,16],[10],40⟩,⟨253,(23),[4,8,12,16],[10],29⟩,⟨253,(24),[4,8,12,16],[10],40⟩,⟨259,(1),[4,8,12],[10],906⟩,⟨259,(3),[4,8,12],[10],907⟩,⟨259,(5),[8,12],[10],143⟩,⟨259,(7),[8,12],[10],143⟩,⟨259,(11),[4,12],[10],52⟩,⟨259,(13),[8,12],[10],143⟩,⟨259,(15),[12],[10],143⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1760
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1761
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1762
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1763
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1764
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1765
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1766
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1767
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1768
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1769
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1770
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1771
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1772
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1773
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1774
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1775
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1776
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1777
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1778
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1779
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1780
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1781
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1782
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1783
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1784
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1785
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1786
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1787
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1788
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1789
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1790
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1791
end Section14Records_12_1760_1792

#print axioms solution
