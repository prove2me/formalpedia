-- Prove2me | solution 1 for Freiman.section14_s0007_records_1696_1728
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T10:16:45.920464+00:00
-- url     : https://prove2.me/submissions/2deab6e2-40e9-48da-8ed5-620602550014

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
namespace Section14Records_7_1696_1728
private theorem valid1696 : RecordDataValid section14Catalog 7 (⟨230,(9),[3,7,15],[10],817⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨817,[1,2,3,6,7,10,11,13,14,15],818⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1697 : RecordDataValid section14Catalog 7 (⟨230,(10),[3,4,7,8,12,15,16],[10],818⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨818,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],819⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1698 : RecordDataValid section14Catalog 7 (⟨230,(10),[3,7],[11],818⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨818,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],819⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1699 : RecordDataValid section14Catalog 7 (⟨230,(11),[3,4,7,8,12,15,16],[10],819⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨819,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],820⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1700 : RecordDataValid section14Catalog 7 (⟨230,(11),[3,7],[11],819⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨819,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],820⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1701 : RecordDataValid section14Catalog 7 (⟨230,(12),[3,7],[11],1066⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1066,[3,5,6,7],1070⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1702 : RecordDataValid section14Catalog 7 (⟨230,(12),[3,7,15],[10],923⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨923,[2,3,6,7,11,14,15],927⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1703 : RecordDataValid section14Catalog 7 (⟨230,(13),[3,4,7,8,12,15,16],[10],821⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨821,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],822⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1704 : RecordDataValid section14Catalog 7 (⟨230,(13),[3,7],[11],1066⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1066,[3,5,6,7],1070⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1705 : RecordDataValid section14Catalog 7 (⟨230,(14),[3,7],[11],1065⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1065,[3,5,6,7],1069⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1706 : RecordDataValid section14Catalog 7 (⟨230,(14),[3,7,15],[10],817⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨817,[1,2,3,6,7,10,11,13,14,15],818⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1707 : RecordDataValid section14Catalog 7 (⟨230,(15),[3,4,7,8,12,15,16],[10],822⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨822,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],823⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1708 : RecordDataValid section14Catalog 7 (⟨230,(15),[3,7],[11],822⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨822,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],823⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1709 : RecordDataValid section14Catalog 7 (⟨230,(16),[3,4,7,8,12,15,16],[10],823⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨823,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],824⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1710 : RecordDataValid section14Catalog 7 (⟨230,(16),[3,7],[11],823⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨823,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],824⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1711 : RecordDataValid section14Catalog 7 (⟨230,(17),[3,7],[11],1067⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1067,[3,5,6,7],1071⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1712 : RecordDataValid section14Catalog 7 (⟨230,(17),[3,7,15],[10],824⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨824,[1,2,3,5,6,7,10,11,13,14,15],825⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1713 : RecordDataValid section14Catalog 7 (⟨230,(18),[3,4,7,8,12,15,16],[10],825⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨825,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],826⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1714 : RecordDataValid section14Catalog 7 (⟨230,(18),[3,7],[11],1067⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1067,[3,5,6,7],1071⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1715 : RecordDataValid section14Catalog 7 (⟨230,(19),[3,7],[11],1067⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1067,[3,5,6,7],1071⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1716 : RecordDataValid section14Catalog 7 (⟨230,(19),[3,7,15],[10],824⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨824,[1,2,3,5,6,7,10,11,13,14,15],825⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1717 : RecordDataValid section14Catalog 7 (⟨230,(20),[3,4,7,8,12,15,16],[10],826⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨826,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],827⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1718 : RecordDataValid section14Catalog 7 (⟨230,(20),[3,7],[11],826⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨826,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],827⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1719 : RecordDataValid section14Catalog 7 (⟨230,(21),[3,4,7,8,12,15,16],[10],827⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨827,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],828⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1720 : RecordDataValid section14Catalog 7 (⟨230,(21),[3,7],[11],827⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨827,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],828⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1721 : RecordDataValid section14Catalog 7 (⟨230,(22),[3,7],[11],1068⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1068,[3,5,6,7],1072⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1722 : RecordDataValid section14Catalog 7 (⟨230,(22),[3,7,15],[10],828⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨828,[1,2,3,5,6,7,10,11,13,14,15],829⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1723 : RecordDataValid section14Catalog 7 (⟨230,(23),[3,4,7,8,12,15,16],[10],829⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨829,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],830⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1724 : RecordDataValid section14Catalog 7 (⟨230,(23),[3,7],[11],1068⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1068,[3,5,6,7],1072⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1725 : RecordDataValid section14Catalog 7 (⟨230,(24),[3,7],[11],1068⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1068,[3,5,6,7],1072⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1726 : RecordDataValid section14Catalog 7 (⟨230,(24),[3,7,15],[10],828⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨828,[1,2,3,5,6,7,10,11,13,14,15],829⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1727 : RecordDataValid section14Catalog 7 (⟨231,(0),[3,7],[11],830⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨830,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],831⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 1696).take 32, section14RecordValid section14Catalog 7 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 1696).take 32 = [⟨230,(9),[3,7,15],[10],817⟩,⟨230,(10),[3,4,7,8,12,15,16],[10],818⟩,⟨230,(10),[3,7],[11],818⟩,⟨230,(11),[3,4,7,8,12,15,16],[10],819⟩,⟨230,(11),[3,7],[11],819⟩,⟨230,(12),[3,7],[11],1066⟩,⟨230,(12),[3,7,15],[10],923⟩,⟨230,(13),[3,4,7,8,12,15,16],[10],821⟩,⟨230,(13),[3,7],[11],1066⟩,⟨230,(14),[3,7],[11],1065⟩,⟨230,(14),[3,7,15],[10],817⟩,⟨230,(15),[3,4,7,8,12,15,16],[10],822⟩,⟨230,(15),[3,7],[11],822⟩,⟨230,(16),[3,4,7,8,12,15,16],[10],823⟩,⟨230,(16),[3,7],[11],823⟩,⟨230,(17),[3,7],[11],1067⟩,⟨230,(17),[3,7,15],[10],824⟩,⟨230,(18),[3,4,7,8,12,15,16],[10],825⟩,⟨230,(18),[3,7],[11],1067⟩,⟨230,(19),[3,7],[11],1067⟩,⟨230,(19),[3,7,15],[10],824⟩,⟨230,(20),[3,4,7,8,12,15,16],[10],826⟩,⟨230,(20),[3,7],[11],826⟩,⟨230,(21),[3,4,7,8,12,15,16],[10],827⟩,⟨230,(21),[3,7],[11],827⟩,⟨230,(22),[3,7],[11],1068⟩,⟨230,(22),[3,7,15],[10],828⟩,⟨230,(23),[3,4,7,8,12,15,16],[10],829⟩,⟨230,(23),[3,7],[11],1068⟩,⟨230,(24),[3,7],[11],1068⟩,⟨230,(24),[3,7,15],[10],828⟩,⟨231,(0),[3,7],[11],830⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1696
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1697
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1698
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1699
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1700
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1701
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1702
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1703
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1704
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1705
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1706
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1707
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1708
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1709
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1710
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1711
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1712
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1713
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1714
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1715
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1716
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1717
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1718
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1719
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1720
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1721
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1722
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1723
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1724
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1725
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1726
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1727
end Section14Records_7_1696_1728

#print axioms solution
