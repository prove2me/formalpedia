-- Prove2me | solution 1 for Freiman.section14_s0012_records_1728_1760
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T05:07:36.057169+00:00
-- url     : https://prove2.me/submissions/06c11059-cfbc-4674-832c-576d1e528211

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
namespace Section14Records_12_1728_1760
private theorem valid1728 : RecordDataValid section14Catalog 12 (⟨238,(15),[3,4,7,8,12,15,16],[10],620⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨620,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],621⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1729 : RecordDataValid section14Catalog 12 (⟨242,(0),[4,8,12],[10],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1730 : RecordDataValid section14Catalog 12 (⟨242,(1),[4,8,12],[10],872⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨872,[1,2,4,5,6,8,9,10,12,13,14,16],873⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1731 : RecordDataValid section14Catalog 12 (⟨242,(2),[4,8,12],[10],873⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨873,[1,2,3,4,5,6,7,8,9,10,11,12],874⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1732 : RecordDataValid section14Catalog 12 (⟨242,(3),[4,8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1733 : RecordDataValid section14Catalog 12 (⟨242,(4),[4,8,12],[10],873⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨873,[1,2,3,4,5,6,7,8,9,10,11,12],874⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1734 : RecordDataValid section14Catalog 12 (⟨242,(5),[4,8,12],[10],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1735 : RecordDataValid section14Catalog 12 (⟨242,(6),[4,8,12],[10],872⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨872,[1,2,4,5,6,8,9,10,12,13,14,16],873⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1736 : RecordDataValid section14Catalog 12 (⟨242,(7),[4,8,12],[10],874⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨874,[1,2,4,5,6,8,9,10,12],875⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1737 : RecordDataValid section14Catalog 12 (⟨242,(8),[4,8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1738 : RecordDataValid section14Catalog 12 (⟨242,(9),[4,8,12],[10],874⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨874,[1,2,4,5,6,8,9,10,12],875⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1739 : RecordDataValid section14Catalog 12 (⟨242,(10),[4,8,12],[10],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1740 : RecordDataValid section14Catalog 12 (⟨242,(11),[4,8,12],[10],872⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨872,[1,2,4,5,6,8,9,10,12,13,14,16],873⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1741 : RecordDataValid section14Catalog 12 (⟨242,(12),[4,8,12],[10],875⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨875,[1,2,4,5,6,8,9,10,12],876⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1742 : RecordDataValid section14Catalog 12 (⟨242,(13),[4,8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1743 : RecordDataValid section14Catalog 12 (⟨242,(14),[4,8,12],[10],875⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨875,[1,2,4,5,6,8,9,10,12],876⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1744 : RecordDataValid section14Catalog 12 (⟨242,(15),[4,8,12],[10],625⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨625,[1,2,4,5,6,8,9,10,12],626⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1745 : RecordDataValid section14Catalog 12 (⟨242,(16),[4,8,12],[10],626⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨626,[1,2,4,5,6,8,9,10,12],627⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1746 : RecordDataValid section14Catalog 12 (⟨242,(17),[4,8,12],[10],286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨286,[1,2,4,5,6,8,9,10,12],287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1747 : RecordDataValid section14Catalog 12 (⟨242,(18),[4,8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1748 : RecordDataValid section14Catalog 12 (⟨242,(19),[4,8,12],[10],286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨286,[1,2,4,5,6,8,9,10,12],287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1749 : RecordDataValid section14Catalog 12 (⟨242,(20),[4,8,12],[10],876⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨876,[1,2,4,5,6,8,9,10,12],877⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1750 : RecordDataValid section14Catalog 12 (⟨242,(21),[4,8,12],[10],877⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨877,[1,2,4,5,6,8,9,10,12],878⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1751 : RecordDataValid section14Catalog 12 (⟨242,(22),[4,8,12],[10],287⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨287,[1,2,4,5,6,8,9,10,12],288⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1752 : RecordDataValid section14Catalog 12 (⟨242,(23),[4,8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1753 : RecordDataValid section14Catalog 12 (⟨242,(24),[4,8,12],[10],287⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨287,[1,2,4,5,6,8,9,10,12],288⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1754 : RecordDataValid section14Catalog 12 (⟨245,(-1),[8,12],[14],1648⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1648,[8,9,12],1653⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1755 : RecordDataValid section14Catalog 12 (⟨245,(-1),[12],[0,4,8,12],1716⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1716,[12],1721⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1756 : RecordDataValid section14Catalog 12 (⟨245,(-1),[12],[1,5,9,13],1717⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1717,[12],1722⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1757 : RecordDataValid section14Catalog 12 (⟨245,(-1),[12],[2],1718⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1718,[12],1723⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1758 : RecordDataValid section14Catalog 12 (⟨245,(-1),[12],[3,7,11,15],1719⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1719,[12],1724⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1759 : RecordDataValid section14Catalog 12 (⟨245,(-1),[12],[6],1720⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1720,[12],1725⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1728).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1728).take 32 = [⟨238,(15),[3,4,7,8,12,15,16],[10],620⟩,⟨242,(0),[4,8,12],[10],632⟩,⟨242,(1),[4,8,12],[10],872⟩,⟨242,(2),[4,8,12],[10],873⟩,⟨242,(3),[4,8,12],[10],101⟩,⟨242,(4),[4,8,12],[10],873⟩,⟨242,(5),[4,8,12],[10],632⟩,⟨242,(6),[4,8,12],[10],872⟩,⟨242,(7),[4,8,12],[10],874⟩,⟨242,(8),[4,8,12],[10],101⟩,⟨242,(9),[4,8,12],[10],874⟩,⟨242,(10),[4,8,12],[10],632⟩,⟨242,(11),[4,8,12],[10],872⟩,⟨242,(12),[4,8,12],[10],875⟩,⟨242,(13),[4,8,12],[10],101⟩,⟨242,(14),[4,8,12],[10],875⟩,⟨242,(15),[4,8,12],[10],625⟩,⟨242,(16),[4,8,12],[10],626⟩,⟨242,(17),[4,8,12],[10],286⟩,⟨242,(18),[4,8,12],[10],101⟩,⟨242,(19),[4,8,12],[10],286⟩,⟨242,(20),[4,8,12],[10],876⟩,⟨242,(21),[4,8,12],[10],877⟩,⟨242,(22),[4,8,12],[10],287⟩,⟨242,(23),[4,8,12],[10],101⟩,⟨242,(24),[4,8,12],[10],287⟩,⟨245,(-1),[8,12],[14],1648⟩,⟨245,(-1),[12],[0,4,8,12],1716⟩,⟨245,(-1),[12],[1,5,9,13],1717⟩,⟨245,(-1),[12],[2],1718⟩,⟨245,(-1),[12],[3,7,11,15],1719⟩,⟨245,(-1),[12],[6],1720⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1728
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1729
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1730
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1731
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1732
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1733
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1734
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1735
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1736
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1737
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1738
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1739
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1740
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1741
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1742
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1743
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1744
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1745
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1746
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1747
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1748
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1749
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1750
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1751
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1752
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1753
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1754
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1755
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1756
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1757
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1758
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1759
end Section14Records_12_1728_1760

#print axioms solution
