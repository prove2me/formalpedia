-- Prove2me | solution 1 for Freiman.section14_s0012_records_1664_1696
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T05:06:05.562225+00:00
-- url     : https://prove2.me/submissions/4e84505a-b2d7-4216-b566-1d4f841d5364

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
namespace Section14Records_12_1664_1696
private theorem valid1664 : RecordDataValid section14Catalog 12 (⟨234,(3),[4,8,12,16],[10],1383⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1383,[4,8,9,12,16],1387⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1665 : RecordDataValid section14Catalog 12 (⟨234,(4),[3,4,7,8,12,15,16],[10],572⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨572,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],573⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1666 : RecordDataValid section14Catalog 12 (⟨234,(5),[4,8,12,16],[10],1384⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1384,[4,8,9,12,16],1388⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1667 : RecordDataValid section14Catalog 12 (⟨234,(6),[4,8,12,16],[10],1384⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1384,[4,8,9,12,16],1388⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1668 : RecordDataValid section14Catalog 12 (⟨234,(7),[4,8,12,16],[10],1384⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1384,[4,8,9,12,16],1388⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1669 : RecordDataValid section14Catalog 12 (⟨234,(8),[3,4,7,8,12,15,16],[10],574⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨574,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],575⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1670 : RecordDataValid section14Catalog 12 (⟨234,(9),[4,8,12,16],[10],1385⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1385,[4,8,9,12,16],1389⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1671 : RecordDataValid section14Catalog 12 (⟨234,(10),[4,8,12,16],[10],1385⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1385,[4,8,9,12,16],1389⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1672 : RecordDataValid section14Catalog 12 (⟨234,(11),[4,8,12,16],[10],1385⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1385,[4,8,9,12,16],1389⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1673 : RecordDataValid section14Catalog 12 (⟨234,(12),[3,4,7,8,12,15,16],[10],576⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨576,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],577⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1674 : RecordDataValid section14Catalog 12 (⟨234,(13),[4,8,12,16],[10],1386⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1386,[4,8,9,12,16],1390⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1675 : RecordDataValid section14Catalog 12 (⟨234,(14),[4,8,12,16],[10],1386⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1386,[4,8,9,12,16],1390⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1676 : RecordDataValid section14Catalog 12 (⟨234,(15),[4,8,12,16],[10],1386⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1386,[4,8,9,12,16],1390⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1677 : RecordDataValid section14Catalog 12 (⟨235,(0),[3,4,7,8,12,15,16],[10],578⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨578,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],579⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1678 : RecordDataValid section14Catalog 12 (⟨235,(1),[3,4,7,8,12,15,16],[10],579⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨579,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],580⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1679 : RecordDataValid section14Catalog 12 (⟨235,(2),[4,8,12,16],[10],1387⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1387,[4,8,9,12,16],1391⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1680 : RecordDataValid section14Catalog 12 (⟨235,(3),[3,4,7,8,12,15,16],[10],581⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨581,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],582⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1681 : RecordDataValid section14Catalog 12 (⟨235,(4),[3,4,7,8,12,15,16],[10],582⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨582,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],583⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1682 : RecordDataValid section14Catalog 12 (⟨235,(5),[3,4,7,8,12,15,16],[10],583⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨583,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],584⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1683 : RecordDataValid section14Catalog 12 (⟨235,(6),[4,8,12,16],[10],1388⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1388,[4,8,9,12,16],1392⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1684 : RecordDataValid section14Catalog 12 (⟨235,(7),[3,4,7,8,12,15,16],[10],585⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨585,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],586⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1685 : RecordDataValid section14Catalog 12 (⟨235,(8),[3,4,7,8,12,15,16],[10],578⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨578,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],579⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1686 : RecordDataValid section14Catalog 12 (⟨235,(9),[3,4,7,8,12,15,16],[10],579⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨579,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],580⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1687 : RecordDataValid section14Catalog 12 (⟨235,(10),[4,8,12,16],[10],1387⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1387,[4,8,9,12,16],1391⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1688 : RecordDataValid section14Catalog 12 (⟨235,(11),[3,4,7,8,12,15,16],[10],581⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨581,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],582⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1689 : RecordDataValid section14Catalog 12 (⟨235,(12),[3,4,7,8,12,15,16],[10],586⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨586,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],587⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1690 : RecordDataValid section14Catalog 12 (⟨235,(13),[3,4,7,8,12,15,16],[10],587⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨587,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],588⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1691 : RecordDataValid section14Catalog 12 (⟨235,(14),[4,8,12,16],[10],1389⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1389,[4,8,9,12,16],1393⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1692 : RecordDataValid section14Catalog 12 (⟨235,(15),[3,4,7,8,12,15,16],[10],589⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨589,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],590⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1693 : RecordDataValid section14Catalog 12 (⟨236,(0),[3,4,8,12,15,16],[10],861⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨861,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],862⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1694 : RecordDataValid section14Catalog 12 (⟨236,(1),[3,4,8,12,15,16],[10],862⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨862,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],863⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1695 : RecordDataValid section14Catalog 12 (⟨236,(2),[4,8,12,16],[10],861⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨861,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],862⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1664).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1664).take 32 = [⟨234,(3),[4,8,12,16],[10],1383⟩,⟨234,(4),[3,4,7,8,12,15,16],[10],572⟩,⟨234,(5),[4,8,12,16],[10],1384⟩,⟨234,(6),[4,8,12,16],[10],1384⟩,⟨234,(7),[4,8,12,16],[10],1384⟩,⟨234,(8),[3,4,7,8,12,15,16],[10],574⟩,⟨234,(9),[4,8,12,16],[10],1385⟩,⟨234,(10),[4,8,12,16],[10],1385⟩,⟨234,(11),[4,8,12,16],[10],1385⟩,⟨234,(12),[3,4,7,8,12,15,16],[10],576⟩,⟨234,(13),[4,8,12,16],[10],1386⟩,⟨234,(14),[4,8,12,16],[10],1386⟩,⟨234,(15),[4,8,12,16],[10],1386⟩,⟨235,(0),[3,4,7,8,12,15,16],[10],578⟩,⟨235,(1),[3,4,7,8,12,15,16],[10],579⟩,⟨235,(2),[4,8,12,16],[10],1387⟩,⟨235,(3),[3,4,7,8,12,15,16],[10],581⟩,⟨235,(4),[3,4,7,8,12,15,16],[10],582⟩,⟨235,(5),[3,4,7,8,12,15,16],[10],583⟩,⟨235,(6),[4,8,12,16],[10],1388⟩,⟨235,(7),[3,4,7,8,12,15,16],[10],585⟩,⟨235,(8),[3,4,7,8,12,15,16],[10],578⟩,⟨235,(9),[3,4,7,8,12,15,16],[10],579⟩,⟨235,(10),[4,8,12,16],[10],1387⟩,⟨235,(11),[3,4,7,8,12,15,16],[10],581⟩,⟨235,(12),[3,4,7,8,12,15,16],[10],586⟩,⟨235,(13),[3,4,7,8,12,15,16],[10],587⟩,⟨235,(14),[4,8,12,16],[10],1389⟩,⟨235,(15),[3,4,7,8,12,15,16],[10],589⟩,⟨236,(0),[3,4,8,12,15,16],[10],861⟩,⟨236,(1),[3,4,8,12,15,16],[10],862⟩,⟨236,(2),[4,8,12,16],[10],861⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1664
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1665
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1666
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1667
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1668
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1669
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1670
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1671
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1672
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1673
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1674
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1675
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1676
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1677
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1678
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1679
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1680
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1681
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1682
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1683
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1684
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1685
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1686
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1687
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1688
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1689
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1690
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1691
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1692
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1693
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1694
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1695
end Section14Records_12_1664_1696

#print axioms solution
