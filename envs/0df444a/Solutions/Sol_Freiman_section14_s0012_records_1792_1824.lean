-- Prove2me | solution 1 for Freiman.section14_s0012_records_1792_1824
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T05:10:44.128461+00:00
-- url     : https://prove2.me/submissions/698e6ea0-d07a-4c1c-82bc-2033c75e6237

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
namespace Section14Records_12_1792_1824
private theorem valid1792 : RecordDataValid section14Catalog 12 (⟨259,(17),[4,12],[10],52⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨52,[1,2,4,9,12],52⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1793 : RecordDataValid section14Catalog 12 (⟨260,(-1),[2,4,6,8,10,12,14,16],[0,4],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1794 : RecordDataValid section14Catalog 12 (⟨260,(-1),[4,8,10,12,16],[8,12],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1795 : RecordDataValid section14Catalog 12 (⟨260,(-1),[4,8,12,16],[1,5,9,13],883⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨883,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],885⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1796 : RecordDataValid section14Catalog 12 (⟨260,(-1),[4,8,12,16],[2],884⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨884,[1,2,4,5,6,8,9,10,12,13,14,16],886⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1797 : RecordDataValid section14Catalog 12 (⟨260,(-1),[4,8,12,16],[7,11,15],886⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨886,[1,2,4,5,6,8,9,10,12,13,14,16],888⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1798 : RecordDataValid section14Catalog 12 (⟨260,(-1),[4,8,12,16],[6],887⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨887,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],889⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1799 : RecordDataValid section14Catalog 12 (⟨260,(-1),[4,8,12,16],[14],909⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨909,[1,2,4,5,6,8,9,10,12,13,14,16],911⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1800 : RecordDataValid section14Catalog 12 (⟨260,(-1),[8,12],[3],886⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨886,[1,2,4,5,6,8,9,10,12,13,14,16],888⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1801 : RecordDataValid section14Catalog 12 (⟨267,(0),[8,12],[10],1086⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1086,[3,5,7,8,9,11,12,15],1090⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1802 : RecordDataValid section14Catalog 12 (⟨267,(1),[8,12],[10],1087⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1087,[3,5,7,8,9,11,12,15],1091⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1803 : RecordDataValid section14Catalog 12 (⟨267,(2),[8,12],[10],1088⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1088,[3,5,7,8,9,11,12,15],1092⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1804 : RecordDataValid section14Catalog 12 (⟨267,(3),[8,12],[10],1089⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1089,[3,5,7,8,9,11,12,15],1093⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1805 : RecordDataValid section14Catalog 12 (⟨267,(4),[8,12],[10],1086⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1086,[3,5,7,8,9,11,12,15],1090⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1806 : RecordDataValid section14Catalog 12 (⟨267,(5),[8,12],[10],1087⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1087,[3,5,7,8,9,11,12,15],1091⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1807 : RecordDataValid section14Catalog 12 (⟨267,(6),[8,12],[10],1090⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1090,[3,5,7,8,9,11,12,15],1094⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1808 : RecordDataValid section14Catalog 12 (⟨267,(7),[8,12],[10],1089⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1089,[3,5,7,8,9,11,12,15],1093⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1809 : RecordDataValid section14Catalog 12 (⟨267,(8),[8,12],[10],1086⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1086,[3,5,7,8,9,11,12,15],1090⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1810 : RecordDataValid section14Catalog 12 (⟨267,(9),[8,12],[10],1087⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1087,[3,5,7,8,9,11,12,15],1091⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1811 : RecordDataValid section14Catalog 12 (⟨267,(10),[8,12],[10],1088⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1088,[3,5,7,8,9,11,12,15],1092⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1812 : RecordDataValid section14Catalog 12 (⟨267,(11),[8,12],[10],1089⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1089,[3,5,7,8,9,11,12,15],1093⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1813 : RecordDataValid section14Catalog 12 (⟨267,(12),[8,12],[10],1086⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1086,[3,5,7,8,9,11,12,15],1090⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1814 : RecordDataValid section14Catalog 12 (⟨267,(13),[8,12],[10],1087⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1087,[3,5,7,8,9,11,12,15],1091⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1815 : RecordDataValid section14Catalog 12 (⟨267,(14),[8,12],[10],1091⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1091,[3,5,7,8,9,11,12,15],1095⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1816 : RecordDataValid section14Catalog 12 (⟨267,(15),[8,12],[10],1089⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1089,[3,5,7,8,9,11,12,15],1093⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1817 : RecordDataValid section14Catalog 12 (⟨270,(0),[8,12],[10],1414⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1414,[5,8,9,12],1419⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1818 : RecordDataValid section14Catalog 12 (⟨270,(1),[8,12],[10],1415⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1415,[5,8,9,12],1420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1819 : RecordDataValid section14Catalog 12 (⟨270,(2),[8,12],[10],1414⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1414,[5,8,9,12],1419⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1820 : RecordDataValid section14Catalog 12 (⟨270,(3),[8,12],[10],1416⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1416,[5,8,9,12],1421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1821 : RecordDataValid section14Catalog 12 (⟨270,(4),[8,12],[10],1417⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1417,[5,8,9,12],1422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1822 : RecordDataValid section14Catalog 12 (⟨270,(5),[8,12],[10],1417⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1417,[5,8,9,12],1422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1823 : RecordDataValid section14Catalog 12 (⟨270,(6),[8,12],[10],1417⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1417,[5,8,9,12],1422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1792).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1792).take 32 = [⟨259,(17),[4,12],[10],52⟩,⟨260,(-1),[2,4,6,8,10,12,14,16],[0,4],882⟩,⟨260,(-1),[4,8,10,12,16],[8,12],882⟩,⟨260,(-1),[4,8,12,16],[1,5,9,13],883⟩,⟨260,(-1),[4,8,12,16],[2],884⟩,⟨260,(-1),[4,8,12,16],[7,11,15],886⟩,⟨260,(-1),[4,8,12,16],[6],887⟩,⟨260,(-1),[4,8,12,16],[14],909⟩,⟨260,(-1),[8,12],[3],886⟩,⟨267,(0),[8,12],[10],1086⟩,⟨267,(1),[8,12],[10],1087⟩,⟨267,(2),[8,12],[10],1088⟩,⟨267,(3),[8,12],[10],1089⟩,⟨267,(4),[8,12],[10],1086⟩,⟨267,(5),[8,12],[10],1087⟩,⟨267,(6),[8,12],[10],1090⟩,⟨267,(7),[8,12],[10],1089⟩,⟨267,(8),[8,12],[10],1086⟩,⟨267,(9),[8,12],[10],1087⟩,⟨267,(10),[8,12],[10],1088⟩,⟨267,(11),[8,12],[10],1089⟩,⟨267,(12),[8,12],[10],1086⟩,⟨267,(13),[8,12],[10],1087⟩,⟨267,(14),[8,12],[10],1091⟩,⟨267,(15),[8,12],[10],1089⟩,⟨270,(0),[8,12],[10],1414⟩,⟨270,(1),[8,12],[10],1415⟩,⟨270,(2),[8,12],[10],1414⟩,⟨270,(3),[8,12],[10],1416⟩,⟨270,(4),[8,12],[10],1417⟩,⟨270,(5),[8,12],[10],1417⟩,⟨270,(6),[8,12],[10],1417⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1792
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1793
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1794
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1795
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1796
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1797
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1798
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1799
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1800
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1801
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1802
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1803
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1804
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1805
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1806
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1807
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1808
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1809
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1810
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1811
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1812
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1813
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1814
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1815
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1816
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1817
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1818
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1819
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1820
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1821
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1822
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1823
end Section14Records_12_1792_1824

#print axioms solution
