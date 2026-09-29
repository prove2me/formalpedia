-- Prove2me | solution 1 for Freiman.section14_s0009_records_1696_1728
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T20:54:27.736919+00:00
-- url     : https://prove2.me/submissions/7611da82-06fa-4e0d-a9ca-7080cc3a6162

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
namespace Section14Records_9_1696_1728
private theorem valid1696 : RecordDataValid section14Catalog 9 (⟨180,(5),[9,10],[42],667⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨667,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],668⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1697 : RecordDataValid section14Catalog 9 (⟨180,(6),[9,10],[42],670⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨670,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],671⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1698 : RecordDataValid section14Catalog 9 (⟨180,(7),[9,10],[42],669⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨669,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],670⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1699 : RecordDataValid section14Catalog 9 (⟨180,(8),[9,10],[42],666⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨666,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],667⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1700 : RecordDataValid section14Catalog 9 (⟨180,(9),[9,10],[42],667⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨667,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],668⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1701 : RecordDataValid section14Catalog 9 (⟨180,(10),[9,10],[42],668⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨668,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],669⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1702 : RecordDataValid section14Catalog 9 (⟨180,(11),[9,10],[42],669⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨669,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],670⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1703 : RecordDataValid section14Catalog 9 (⟨180,(12),[9,10],[42],666⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨666,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],667⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1704 : RecordDataValid section14Catalog 9 (⟨180,(13),[9,10],[42],667⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨667,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],668⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1705 : RecordDataValid section14Catalog 9 (⟨180,(14),[9,10],[42],671⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨671,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],672⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1706 : RecordDataValid section14Catalog 9 (⟨180,(15),[9,10],[42],669⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨669,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],670⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1707 : RecordDataValid section14Catalog 9 (⟨183,(0),[9],[42],1303⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1303,[4,8,9,12,16],1307⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1708 : RecordDataValid section14Catalog 9 (⟨183,(1),[9],[42],1304⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1304,[4,8,9,12,16],1308⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1709 : RecordDataValid section14Catalog 9 (⟨183,(2),[9],[42],1303⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1303,[4,8,9,12,16],1307⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1710 : RecordDataValid section14Catalog 9 (⟨183,(3),[9],[42],1305⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1305,[4,8,9,12,16],1309⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1711 : RecordDataValid section14Catalog 9 (⟨183,(4),[9],[42],1306⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1306,[4,8,9,12,16],1310⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1712 : RecordDataValid section14Catalog 9 (⟨183,(5),[9],[42],1306⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1306,[4,8,9,12,16],1310⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1713 : RecordDataValid section14Catalog 9 (⟨183,(6),[9],[42],1306⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1306,[4,8,9,12,16],1310⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1714 : RecordDataValid section14Catalog 9 (⟨183,(7),[9],[42],1306⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1306,[4,8,9,12,16],1310⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1715 : RecordDataValid section14Catalog 9 (⟨183,(8),[9],[42],1307⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1307,[4,8,9,12,16],1311⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1716 : RecordDataValid section14Catalog 9 (⟨183,(9),[9],[42],1307⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1307,[4,8,9,12,16],1311⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1717 : RecordDataValid section14Catalog 9 (⟨183,(10),[9],[42],1307⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1307,[4,8,9,12,16],1311⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1718 : RecordDataValid section14Catalog 9 (⟨183,(11),[9],[42],1307⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1307,[4,8,9,12,16],1311⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1719 : RecordDataValid section14Catalog 9 (⟨183,(12),[9],[42],1308⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1308,[4,8,9,12,16],1312⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1720 : RecordDataValid section14Catalog 9 (⟨183,(13),[9],[42],1308⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1308,[4,8,9,12,16],1312⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1721 : RecordDataValid section14Catalog 9 (⟨183,(14),[9],[42],1308⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1308,[4,8,9,12,16],1312⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1722 : RecordDataValid section14Catalog 9 (⟨183,(15),[9],[42],1308⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1308,[4,8,9,12,16],1312⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1723 : RecordDataValid section14Catalog 9 (⟨185,(0),[9,10],[42],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1724 : RecordDataValid section14Catalog 9 (⟨185,(1),[9,10],[42],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1725 : RecordDataValid section14Catalog 9 (⟨185,(2),[9,10],[42],680⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨680,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],681⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1726 : RecordDataValid section14Catalog 9 (⟨185,(3),[9,10],[42],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1727 : RecordDataValid section14Catalog 9 (⟨185,(4),[9,10],[42],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 1696).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 1696).take 32 = [⟨180,(5),[9,10],[42],667⟩,⟨180,(6),[9,10],[42],670⟩,⟨180,(7),[9,10],[42],669⟩,⟨180,(8),[9,10],[42],666⟩,⟨180,(9),[9,10],[42],667⟩,⟨180,(10),[9,10],[42],668⟩,⟨180,(11),[9,10],[42],669⟩,⟨180,(12),[9,10],[42],666⟩,⟨180,(13),[9,10],[42],667⟩,⟨180,(14),[9,10],[42],671⟩,⟨180,(15),[9,10],[42],669⟩,⟨183,(0),[9],[42],1303⟩,⟨183,(1),[9],[42],1304⟩,⟨183,(2),[9],[42],1303⟩,⟨183,(3),[9],[42],1305⟩,⟨183,(4),[9],[42],1306⟩,⟨183,(5),[9],[42],1306⟩,⟨183,(6),[9],[42],1306⟩,⟨183,(7),[9],[42],1306⟩,⟨183,(8),[9],[42],1307⟩,⟨183,(9),[9],[42],1307⟩,⟨183,(10),[9],[42],1307⟩,⟨183,(11),[9],[42],1307⟩,⟨183,(12),[9],[42],1308⟩,⟨183,(13),[9],[42],1308⟩,⟨183,(14),[9],[42],1308⟩,⟨183,(15),[9],[42],1308⟩,⟨185,(0),[9,10],[42],678⟩,⟨185,(1),[9,10],[42],679⟩,⟨185,(2),[9,10],[42],680⟩,⟨185,(3),[9,10],[42],681⟩,⟨185,(4),[9,10],[42],678⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1696
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1697
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1698
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1699
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1700
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1701
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1702
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1703
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1704
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1705
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1706
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1707
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1708
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1709
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1710
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1711
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1712
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1713
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1714
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1715
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1716
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1717
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1718
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1719
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1720
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1721
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1722
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1723
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1724
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1725
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1726
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1727
end Section14Records_9_1696_1728

#print axioms solution
