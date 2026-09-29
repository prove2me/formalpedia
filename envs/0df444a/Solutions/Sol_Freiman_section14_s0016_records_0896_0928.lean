-- Prove2me | solution 1 for Freiman.section14_s0016_records_0896_0928
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T23:11:07.756138+00:00
-- url     : https://prove2.me/submissions/ecdc2c84-7f47-47bb-83df-9ca393515c46

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
namespace Section14Records_16_896_928
private theorem valid896 : RecordDataValid section14Catalog 16 (⟨157,(9),[4,8,16],[10],1275⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1275,[4,8,9,12,16],1279⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid897 : RecordDataValid section14Catalog 16 (⟨157,(10),[3,4,7,8,15,16],[10],18⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨18,[1,2,3,4,5,6,7,8,13,14,15,16],18⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid898 : RecordDataValid section14Catalog 16 (⟨157,(11),[4,8,16],[10],1276⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1276,[4,8,16],1280⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid899 : RecordDataValid section14Catalog 16 (⟨157,(12),[4,8,16],[10],1276⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1276,[4,8,16],1280⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid900 : RecordDataValid section14Catalog 16 (⟨157,(13),[4,8,16],[10],1276⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1276,[4,8,16],1280⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid901 : RecordDataValid section14Catalog 16 (⟨157,(14),[4,8,16],[10],1275⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1275,[4,8,9,12,16],1279⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid902 : RecordDataValid section14Catalog 16 (⟨157,(15),[3,4,7,8,15,16],[10],21⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨21,[1,2,3,4,5,6,7,8,13,14,15,16],21⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid903 : RecordDataValid section14Catalog 16 (⟨157,(16),[4,8,16],[10],1277⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1277,[4,8,16],1281⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid904 : RecordDataValid section14Catalog 16 (⟨157,(17),[4,8,16],[10],1277⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1277,[4,8,16],1281⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid905 : RecordDataValid section14Catalog 16 (⟨157,(18),[4,8,16],[10],1277⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1277,[4,8,16],1281⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid906 : RecordDataValid section14Catalog 16 (⟨157,(19),[4,8,16],[10],1277⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1277,[4,8,16],1281⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid907 : RecordDataValid section14Catalog 16 (⟨157,(20),[3,4,7,8,15,16],[10],24⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨24,[1,2,3,4,5,6,7,8,13,14,15,16],24⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid908 : RecordDataValid section14Catalog 16 (⟨157,(21),[4,8,16],[10],1278⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1278,[4,8,16],1282⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid909 : RecordDataValid section14Catalog 16 (⟨157,(22),[4,8,16],[10],1278⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1278,[4,8,16],1282⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid910 : RecordDataValid section14Catalog 16 (⟨157,(23),[4,8,16],[10],1278⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1278,[4,8,16],1282⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid911 : RecordDataValid section14Catalog 16 (⟨157,(24),[4,8,16],[10],1278⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1278,[4,8,16],1282⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid912 : RecordDataValid section14Catalog 16 (⟨160,(0),[3,4,8,12,15,16],[10],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid913 : RecordDataValid section14Catalog 16 (⟨160,(1),[3,4,8,12,15,16],[10],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid914 : RecordDataValid section14Catalog 16 (⟨160,(2),[3,4,8,12,15,16],[10],640⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨640,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],641⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid915 : RecordDataValid section14Catalog 16 (⟨160,(3),[3,4,8,12,15,16],[10],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid916 : RecordDataValid section14Catalog 16 (⟨160,(4),[3,4,8,12,15,16],[10],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid917 : RecordDataValid section14Catalog 16 (⟨160,(5),[3,4,8,12,15,16],[10],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid918 : RecordDataValid section14Catalog 16 (⟨160,(6),[3,4,8,12,15,16],[10],642⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨642,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],643⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid919 : RecordDataValid section14Catalog 16 (⟨160,(7),[3,4,8,12,15,16],[10],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid920 : RecordDataValid section14Catalog 16 (⟨160,(8),[3,4,8,12,15,16],[10],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid921 : RecordDataValid section14Catalog 16 (⟨160,(9),[3,4,8,12,15,16],[10],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid922 : RecordDataValid section14Catalog 16 (⟨160,(10),[3,4,8,12,15,16],[10],640⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨640,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],641⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid923 : RecordDataValid section14Catalog 16 (⟨160,(11),[3,4,8,12,15,16],[10],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid924 : RecordDataValid section14Catalog 16 (⟨160,(12),[3,4,8,12,15,16],[10],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid925 : RecordDataValid section14Catalog 16 (⟨160,(13),[3,4,8,12,15,16],[10],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid926 : RecordDataValid section14Catalog 16 (⟨160,(14),[3,4,8,12,15,16],[10],643⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨643,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],644⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid927 : RecordDataValid section14Catalog 16 (⟨160,(15),[3,4,8,12,15,16],[10],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 896).take 32, section14RecordValid section14Catalog 16 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 896).take 32 = [⟨157,(9),[4,8,16],[10],1275⟩,⟨157,(10),[3,4,7,8,15,16],[10],18⟩,⟨157,(11),[4,8,16],[10],1276⟩,⟨157,(12),[4,8,16],[10],1276⟩,⟨157,(13),[4,8,16],[10],1276⟩,⟨157,(14),[4,8,16],[10],1275⟩,⟨157,(15),[3,4,7,8,15,16],[10],21⟩,⟨157,(16),[4,8,16],[10],1277⟩,⟨157,(17),[4,8,16],[10],1277⟩,⟨157,(18),[4,8,16],[10],1277⟩,⟨157,(19),[4,8,16],[10],1277⟩,⟨157,(20),[3,4,7,8,15,16],[10],24⟩,⟨157,(21),[4,8,16],[10],1278⟩,⟨157,(22),[4,8,16],[10],1278⟩,⟨157,(23),[4,8,16],[10],1278⟩,⟨157,(24),[4,8,16],[10],1278⟩,⟨160,(0),[3,4,8,12,15,16],[10],638⟩,⟨160,(1),[3,4,8,12,15,16],[10],639⟩,⟨160,(2),[3,4,8,12,15,16],[10],640⟩,⟨160,(3),[3,4,8,12,15,16],[10],641⟩,⟨160,(4),[3,4,8,12,15,16],[10],638⟩,⟨160,(5),[3,4,8,12,15,16],[10],639⟩,⟨160,(6),[3,4,8,12,15,16],[10],642⟩,⟨160,(7),[3,4,8,12,15,16],[10],641⟩,⟨160,(8),[3,4,8,12,15,16],[10],638⟩,⟨160,(9),[3,4,8,12,15,16],[10],639⟩,⟨160,(10),[3,4,8,12,15,16],[10],640⟩,⟨160,(11),[3,4,8,12,15,16],[10],641⟩,⟨160,(12),[3,4,8,12,15,16],[10],638⟩,⟨160,(13),[3,4,8,12,15,16],[10],639⟩,⟨160,(14),[3,4,8,12,15,16],[10],643⟩,⟨160,(15),[3,4,8,12,15,16],[10],641⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 16 _ hnum valid896
  · exact recordValid_of_data section14Catalog 16 _ hnum valid897
  · exact recordValid_of_data section14Catalog 16 _ hnum valid898
  · exact recordValid_of_data section14Catalog 16 _ hnum valid899
  · exact recordValid_of_data section14Catalog 16 _ hnum valid900
  · exact recordValid_of_data section14Catalog 16 _ hnum valid901
  · exact recordValid_of_data section14Catalog 16 _ hnum valid902
  · exact recordValid_of_data section14Catalog 16 _ hnum valid903
  · exact recordValid_of_data section14Catalog 16 _ hnum valid904
  · exact recordValid_of_data section14Catalog 16 _ hnum valid905
  · exact recordValid_of_data section14Catalog 16 _ hnum valid906
  · exact recordValid_of_data section14Catalog 16 _ hnum valid907
  · exact recordValid_of_data section14Catalog 16 _ hnum valid908
  · exact recordValid_of_data section14Catalog 16 _ hnum valid909
  · exact recordValid_of_data section14Catalog 16 _ hnum valid910
  · exact recordValid_of_data section14Catalog 16 _ hnum valid911
  · exact recordValid_of_data section14Catalog 16 _ hnum valid912
  · exact recordValid_of_data section14Catalog 16 _ hnum valid913
  · exact recordValid_of_data section14Catalog 16 _ hnum valid914
  · exact recordValid_of_data section14Catalog 16 _ hnum valid915
  · exact recordValid_of_data section14Catalog 16 _ hnum valid916
  · exact recordValid_of_data section14Catalog 16 _ hnum valid917
  · exact recordValid_of_data section14Catalog 16 _ hnum valid918
  · exact recordValid_of_data section14Catalog 16 _ hnum valid919
  · exact recordValid_of_data section14Catalog 16 _ hnum valid920
  · exact recordValid_of_data section14Catalog 16 _ hnum valid921
  · exact recordValid_of_data section14Catalog 16 _ hnum valid922
  · exact recordValid_of_data section14Catalog 16 _ hnum valid923
  · exact recordValid_of_data section14Catalog 16 _ hnum valid924
  · exact recordValid_of_data section14Catalog 16 _ hnum valid925
  · exact recordValid_of_data section14Catalog 16 _ hnum valid926
  · exact recordValid_of_data section14Catalog 16 _ hnum valid927
end Section14Records_16_896_928

#print axioms solution
