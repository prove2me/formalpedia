-- Prove2me | solution 1 for Freiman.section14_s0010_records_1696_1728
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T17:16:43.058996+00:00
-- url     : https://prove2.me/submissions/21025b66-7701-4cb4-a6d0-62ac78777306

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
namespace Section14Records_10_1696_1728
private theorem valid1696 : RecordDataValid section14Catalog 10 (⟨180,(15),[9,10],[42],669⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨669,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],670⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1697 : RecordDataValid section14Catalog 10 (⟨183,(0),[10],[42],672⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨672,[1,2,3,5,6,7,10,11,13,14,15],673⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1698 : RecordDataValid section14Catalog 10 (⟨183,(1),[10],[42],673⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨673,[1,2,3,5,6,7,10,11,13,14,15],674⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1699 : RecordDataValid section14Catalog 10 (⟨183,(2),[10],[42],672⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨672,[1,2,3,5,6,7,10,11,13,14,15],673⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1700 : RecordDataValid section14Catalog 10 (⟨183,(3),[10],[42],674⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨674,[1,2,3,5,6,7,10,11,13,14,15],675⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1701 : RecordDataValid section14Catalog 10 (⟨183,(4),[10],[42],675⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨675,[1,2,3,5,6,7,10,11,13,14,15],676⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1702 : RecordDataValid section14Catalog 10 (⟨183,(5),[10],[42],675⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨675,[1,2,3,5,6,7,10,11,13,14,15],676⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1703 : RecordDataValid section14Catalog 10 (⟨183,(6),[10],[42],675⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨675,[1,2,3,5,6,7,10,11,13,14,15],676⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1704 : RecordDataValid section14Catalog 10 (⟨183,(7),[10],[42],675⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨675,[1,2,3,5,6,7,10,11,13,14,15],676⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1705 : RecordDataValid section14Catalog 10 (⟨183,(8),[10],[42],676⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨676,[1,2,3,5,6,7,10,11,13,14,15],677⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1706 : RecordDataValid section14Catalog 10 (⟨183,(9),[10],[42],676⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨676,[1,2,3,5,6,7,10,11,13,14,15],677⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1707 : RecordDataValid section14Catalog 10 (⟨183,(10),[10],[42],676⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨676,[1,2,3,5,6,7,10,11,13,14,15],677⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1708 : RecordDataValid section14Catalog 10 (⟨183,(11),[10],[42],676⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨676,[1,2,3,5,6,7,10,11,13,14,15],677⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1709 : RecordDataValid section14Catalog 10 (⟨183,(12),[10],[42],677⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨677,[1,2,3,5,6,7,10,11,13,14,15],678⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1710 : RecordDataValid section14Catalog 10 (⟨183,(13),[10],[42],677⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨677,[1,2,3,5,6,7,10,11,13,14,15],678⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1711 : RecordDataValid section14Catalog 10 (⟨183,(14),[10],[42],677⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨677,[1,2,3,5,6,7,10,11,13,14,15],678⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1712 : RecordDataValid section14Catalog 10 (⟨183,(15),[10],[42],677⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨677,[1,2,3,5,6,7,10,11,13,14,15],678⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1713 : RecordDataValid section14Catalog 10 (⟨185,(0),[9,10],[42],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1714 : RecordDataValid section14Catalog 10 (⟨185,(1),[9,10],[42],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1715 : RecordDataValid section14Catalog 10 (⟨185,(2),[9,10],[42],680⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨680,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],681⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1716 : RecordDataValid section14Catalog 10 (⟨185,(3),[9,10],[42],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1717 : RecordDataValid section14Catalog 10 (⟨185,(4),[9,10],[42],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1718 : RecordDataValid section14Catalog 10 (⟨185,(5),[9,10],[42],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1719 : RecordDataValid section14Catalog 10 (⟨185,(6),[9,10],[42],682⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨682,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],683⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1720 : RecordDataValid section14Catalog 10 (⟨185,(7),[9,10],[42],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1721 : RecordDataValid section14Catalog 10 (⟨185,(8),[9,10],[42],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1722 : RecordDataValid section14Catalog 10 (⟨185,(9),[9,10],[42],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1723 : RecordDataValid section14Catalog 10 (⟨185,(10),[9,10],[42],680⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨680,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],681⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1724 : RecordDataValid section14Catalog 10 (⟨185,(11),[9,10],[42],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1725 : RecordDataValid section14Catalog 10 (⟨185,(12),[9,10],[42],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1726 : RecordDataValid section14Catalog 10 (⟨185,(13),[9,10],[42],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1727 : RecordDataValid section14Catalog 10 (⟨185,(14),[9,10],[42],683⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨683,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],684⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 1696).take 32, section14RecordValid section14Catalog 10 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 1696).take 32 = [⟨180,(15),[9,10],[42],669⟩,⟨183,(0),[10],[42],672⟩,⟨183,(1),[10],[42],673⟩,⟨183,(2),[10],[42],672⟩,⟨183,(3),[10],[42],674⟩,⟨183,(4),[10],[42],675⟩,⟨183,(5),[10],[42],675⟩,⟨183,(6),[10],[42],675⟩,⟨183,(7),[10],[42],675⟩,⟨183,(8),[10],[42],676⟩,⟨183,(9),[10],[42],676⟩,⟨183,(10),[10],[42],676⟩,⟨183,(11),[10],[42],676⟩,⟨183,(12),[10],[42],677⟩,⟨183,(13),[10],[42],677⟩,⟨183,(14),[10],[42],677⟩,⟨183,(15),[10],[42],677⟩,⟨185,(0),[9,10],[42],678⟩,⟨185,(1),[9,10],[42],679⟩,⟨185,(2),[9,10],[42],680⟩,⟨185,(3),[9,10],[42],681⟩,⟨185,(4),[9,10],[42],678⟩,⟨185,(5),[9,10],[42],679⟩,⟨185,(6),[9,10],[42],682⟩,⟨185,(7),[9,10],[42],681⟩,⟨185,(8),[9,10],[42],678⟩,⟨185,(9),[9,10],[42],679⟩,⟨185,(10),[9,10],[42],680⟩,⟨185,(11),[9,10],[42],681⟩,⟨185,(12),[9,10],[42],678⟩,⟨185,(13),[9,10],[42],679⟩,⟨185,(14),[9,10],[42],683⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1696
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1697
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1698
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1699
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1700
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1701
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1702
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1703
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1704
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1705
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1706
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1707
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1708
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1709
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1710
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1711
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1712
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1713
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1714
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1715
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1716
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1717
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1718
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1719
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1720
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1721
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1722
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1723
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1724
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1725
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1726
  · exact recordValid_of_data section14Catalog 10 _ hnum valid1727
end Section14Records_10_1696_1728

#print axioms solution
