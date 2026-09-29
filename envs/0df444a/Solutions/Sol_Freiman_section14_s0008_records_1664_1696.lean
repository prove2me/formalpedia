-- Prove2me | solution 1 for Freiman.section14_s0008_records_1664_1696
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T07:36:25.976476+00:00
-- url     : https://prove2.me/submissions/06a0812a-b866-494a-952e-f295be80897e

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
namespace Section14Records_8_1664_1696
private theorem valid1664 : RecordDataValid section14Catalog 8 (⟨226,(1),[3,4,7,8,12,15,16],[10],767⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨767,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],768⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1665 : RecordDataValid section14Catalog 8 (⟨226,(2),[3,4,7,8,12,15,16],[10],768⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨768,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],769⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1666 : RecordDataValid section14Catalog 8 (⟨226,(3),[3,4,7,8,12,15,16],[10],767⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨767,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],768⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1667 : RecordDataValid section14Catalog 8 (⟨226,(4),[3,4,7,8,12,15,16],[10],769⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨769,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],770⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1668 : RecordDataValid section14Catalog 8 (⟨226,(5),[3,4,7,8,12,15,16],[10],770⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨770,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],771⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1669 : RecordDataValid section14Catalog 8 (⟨226,(6),[3,4,7,8,12,15,16],[10],771⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨771,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],772⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1670 : RecordDataValid section14Catalog 8 (⟨226,(7),[3,4,7,8,12,15,16],[10],771⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨771,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],772⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1671 : RecordDataValid section14Catalog 8 (⟨226,(8),[3,4,7,8,12,15,16],[10],772⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨772,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],773⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1672 : RecordDataValid section14Catalog 8 (⟨226,(9),[3,4,7,8,12,15,16],[10],772⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨772,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],773⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1673 : RecordDataValid section14Catalog 8 (⟨227,(0),[3,4,7,8,12,15,16],[10],773⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨773,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],774⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1674 : RecordDataValid section14Catalog 8 (⟨227,(1),[3,4,7,8,12,15,16],[10],774⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨774,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],775⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1675 : RecordDataValid section14Catalog 8 (⟨227,(2),[4,8,12,16],[10],1371⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1371,[4,8,9,12,16],1375⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1676 : RecordDataValid section14Catalog 8 (⟨227,(3),[3,4,7,8,12,15,16],[10],776⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨776,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],777⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1677 : RecordDataValid section14Catalog 8 (⟨227,(4),[4,8,12,16],[10],1371⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1371,[4,8,9,12,16],1375⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1678 : RecordDataValid section14Catalog 8 (⟨227,(5),[3,4,7,8,12,15,16],[10],773⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨773,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],774⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1679 : RecordDataValid section14Catalog 8 (⟨227,(6),[3,4,7,8,12,15,16],[10],774⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨774,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],775⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1680 : RecordDataValid section14Catalog 8 (⟨227,(7),[4,8,12,16],[10],1371⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1371,[4,8,9,12,16],1375⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1681 : RecordDataValid section14Catalog 8 (⟨227,(8),[3,4,7,8,12,15,16],[10],776⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨776,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],777⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1682 : RecordDataValid section14Catalog 8 (⟨227,(9),[4,8,12,16],[10],1371⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1371,[4,8,9,12,16],1375⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1683 : RecordDataValid section14Catalog 8 (⟨227,(10),[3,4,7,8,12,15,16],[10],777⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨777,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],778⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1684 : RecordDataValid section14Catalog 8 (⟨227,(11),[3,4,7,8,12,15,16],[10],778⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨778,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],779⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1685 : RecordDataValid section14Catalog 8 (⟨227,(12),[4,8,12,16],[10],1372⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1372,[4,8,9,12,16],1376⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1686 : RecordDataValid section14Catalog 8 (⟨227,(13),[3,4,7,8,12,15,16],[10],780⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨780,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],781⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1687 : RecordDataValid section14Catalog 8 (⟨227,(14),[4,8,12,16],[10],1372⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1372,[4,8,9,12,16],1376⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1688 : RecordDataValid section14Catalog 8 (⟨227,(15),[3,4,7,8,12,15,16],[10],781⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨781,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],782⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1689 : RecordDataValid section14Catalog 8 (⟨227,(16),[3,4,7,8,12,15,16],[10],782⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨782,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],783⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1690 : RecordDataValid section14Catalog 8 (⟨227,(17),[4,8,12,16],[10],1373⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1373,[4,8,9,12,16],1377⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1691 : RecordDataValid section14Catalog 8 (⟨227,(18),[3,4,7,8,12,15,16],[10],784⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨784,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],785⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1692 : RecordDataValid section14Catalog 8 (⟨227,(19),[4,8,12,16],[10],1373⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1373,[4,8,9,12,16],1377⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1693 : RecordDataValid section14Catalog 8 (⟨227,(20),[3,4,7,8,12,15,16],[10],785⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨785,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],786⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1694 : RecordDataValid section14Catalog 8 (⟨227,(21),[3,4,7,8,12,15,16],[10],786⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨786,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],787⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1695 : RecordDataValid section14Catalog 8 (⟨227,(22),[4,8,12,16],[10],1374⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1374,[4,8,9,12,16],1378⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1664).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 1664).take 32 = [⟨226,(1),[3,4,7,8,12,15,16],[10],767⟩,⟨226,(2),[3,4,7,8,12,15,16],[10],768⟩,⟨226,(3),[3,4,7,8,12,15,16],[10],767⟩,⟨226,(4),[3,4,7,8,12,15,16],[10],769⟩,⟨226,(5),[3,4,7,8,12,15,16],[10],770⟩,⟨226,(6),[3,4,7,8,12,15,16],[10],771⟩,⟨226,(7),[3,4,7,8,12,15,16],[10],771⟩,⟨226,(8),[3,4,7,8,12,15,16],[10],772⟩,⟨226,(9),[3,4,7,8,12,15,16],[10],772⟩,⟨227,(0),[3,4,7,8,12,15,16],[10],773⟩,⟨227,(1),[3,4,7,8,12,15,16],[10],774⟩,⟨227,(2),[4,8,12,16],[10],1371⟩,⟨227,(3),[3,4,7,8,12,15,16],[10],776⟩,⟨227,(4),[4,8,12,16],[10],1371⟩,⟨227,(5),[3,4,7,8,12,15,16],[10],773⟩,⟨227,(6),[3,4,7,8,12,15,16],[10],774⟩,⟨227,(7),[4,8,12,16],[10],1371⟩,⟨227,(8),[3,4,7,8,12,15,16],[10],776⟩,⟨227,(9),[4,8,12,16],[10],1371⟩,⟨227,(10),[3,4,7,8,12,15,16],[10],777⟩,⟨227,(11),[3,4,7,8,12,15,16],[10],778⟩,⟨227,(12),[4,8,12,16],[10],1372⟩,⟨227,(13),[3,4,7,8,12,15,16],[10],780⟩,⟨227,(14),[4,8,12,16],[10],1372⟩,⟨227,(15),[3,4,7,8,12,15,16],[10],781⟩,⟨227,(16),[3,4,7,8,12,15,16],[10],782⟩,⟨227,(17),[4,8,12,16],[10],1373⟩,⟨227,(18),[3,4,7,8,12,15,16],[10],784⟩,⟨227,(19),[4,8,12,16],[10],1373⟩,⟨227,(20),[3,4,7,8,12,15,16],[10],785⟩,⟨227,(21),[3,4,7,8,12,15,16],[10],786⟩,⟨227,(22),[4,8,12,16],[10],1374⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1664
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1665
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1666
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1667
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1668
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1669
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1670
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1671
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1672
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1673
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1674
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1675
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1676
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1677
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1678
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1679
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1680
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1681
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1682
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1683
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1684
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1685
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1686
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1687
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1688
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1689
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1690
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1691
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1692
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1693
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1694
  · exact recordValid_of_data section14Catalog 8 _ hnum valid1695
end Section14Records_8_1664_1696

#print axioms solution
