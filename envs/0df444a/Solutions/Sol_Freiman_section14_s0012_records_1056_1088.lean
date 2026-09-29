-- Prove2me | solution 1 for Freiman.section14_s0012_records_1056_1088
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T04:45:33.913224+00:00
-- url     : https://prove2.me/submissions/d0fc0a33-b9e3-45c2-94b4-e40ddabed3e8

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
namespace Section14Records_12_1056_1088
private theorem valid1056 : RecordDataValid section14Catalog 12 (⟨167,(9),[4,8,12,16],[10],1286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1286,[4,8,9,12,16],1290⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1057 : RecordDataValid section14Catalog 12 (⟨167,(10),[4,8,12,16],[10],1287⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1287,[4,8,9,12,16],1291⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1058 : RecordDataValid section14Catalog 12 (⟨167,(11),[4,8,12,16],[10],1288⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1288,[4,8,9,12,16],1292⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1059 : RecordDataValid section14Catalog 12 (⟨167,(12),[4,8,12,16],[10],1290⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1290,[4,8,9,12,16],1294⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1060 : RecordDataValid section14Catalog 12 (⟨167,(13),[4,8,12,16],[10],1286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1286,[4,8,9,12,16],1290⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1061 : RecordDataValid section14Catalog 12 (⟨167,(14),[4,8,12,16],[10],1287⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1287,[4,8,9,12,16],1291⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1062 : RecordDataValid section14Catalog 12 (⟨167,(15),[4,8,12,16],[10],1288⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1288,[4,8,9,12,16],1292⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1063 : RecordDataValid section14Catalog 12 (⟨171,(0),[3,4,8,12,15,16],[10],650⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨650,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],651⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1064 : RecordDataValid section14Catalog 12 (⟨171,(1),[3,4,8,12,15,16],[10],651⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨651,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],652⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1065 : RecordDataValid section14Catalog 12 (⟨171,(2),[3,4,8,12,15,16],[10],652⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨652,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],653⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1066 : RecordDataValid section14Catalog 12 (⟨171,(3),[3,4,8,12,15,16],[10],653⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨653,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],654⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1067 : RecordDataValid section14Catalog 12 (⟨172,(0),[4,8,12,16],[10],1291⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1291,[4,8,9,12,16],1295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1068 : RecordDataValid section14Catalog 12 (⟨172,(1),[4,8,12,16],[10],1292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1292,[4,8,9,12,16],1296⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1069 : RecordDataValid section14Catalog 12 (⟨172,(2),[4,8,12,16],[10],1293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1293,[4,8,9,12,16],1297⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1070 : RecordDataValid section14Catalog 12 (⟨172,(3),[4,8,12,16],[10],1294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1294,[4,8,9,12,16],1298⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1071 : RecordDataValid section14Catalog 12 (⟨172,(4),[4,8,12,16],[10],1295⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1295,[4,8,9,12,16],1299⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1072 : RecordDataValid section14Catalog 12 (⟨172,(5),[4,8,12,16],[10],1292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1292,[4,8,9,12,16],1296⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1073 : RecordDataValid section14Catalog 12 (⟨172,(6),[4,8,12,16],[10],1293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1293,[4,8,9,12,16],1297⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1074 : RecordDataValid section14Catalog 12 (⟨172,(7),[4,8,12,16],[10],1294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1294,[4,8,9,12,16],1298⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1075 : RecordDataValid section14Catalog 12 (⟨172,(8),[4,8,12,16],[10],1291⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1291,[4,8,9,12,16],1295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1076 : RecordDataValid section14Catalog 12 (⟨172,(9),[4,8,12,16],[10],1292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1292,[4,8,9,12,16],1296⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1077 : RecordDataValid section14Catalog 12 (⟨172,(10),[4,8,12,16],[10],1293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1293,[4,8,9,12,16],1297⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1078 : RecordDataValid section14Catalog 12 (⟨172,(11),[4,8,12,16],[10],1294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1294,[4,8,9,12,16],1298⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1079 : RecordDataValid section14Catalog 12 (⟨172,(12),[4,8,12,16],[10],1296⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1296,[4,8,9,12,16],1300⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1080 : RecordDataValid section14Catalog 12 (⟨172,(13),[4,8,12,16],[10],1292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1292,[4,8,9,12,16],1296⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1081 : RecordDataValid section14Catalog 12 (⟨172,(14),[4,8,12,16],[10],1293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1293,[4,8,9,12,16],1297⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1082 : RecordDataValid section14Catalog 12 (⟨172,(15),[4,8,12,16],[10],1294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1294,[4,8,9,12,16],1298⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1083 : RecordDataValid section14Catalog 12 (⟨175,(0),[3,4,8,12,15,16],[10],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1084 : RecordDataValid section14Catalog 12 (⟨175,(1),[3,4,8,12,15,16],[10],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1085 : RecordDataValid section14Catalog 12 (⟨175,(2),[3,4,8,12,15,16],[10],656⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨656,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],657⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1086 : RecordDataValid section14Catalog 12 (⟨175,(3),[3,4,8,12,15,16],[10],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1087 : RecordDataValid section14Catalog 12 (⟨175,(4),[3,4,8,12,15,16],[10],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1056).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1056).take 32 = [⟨167,(9),[4,8,12,16],[10],1286⟩,⟨167,(10),[4,8,12,16],[10],1287⟩,⟨167,(11),[4,8,12,16],[10],1288⟩,⟨167,(12),[4,8,12,16],[10],1290⟩,⟨167,(13),[4,8,12,16],[10],1286⟩,⟨167,(14),[4,8,12,16],[10],1287⟩,⟨167,(15),[4,8,12,16],[10],1288⟩,⟨171,(0),[3,4,8,12,15,16],[10],650⟩,⟨171,(1),[3,4,8,12,15,16],[10],651⟩,⟨171,(2),[3,4,8,12,15,16],[10],652⟩,⟨171,(3),[3,4,8,12,15,16],[10],653⟩,⟨172,(0),[4,8,12,16],[10],1291⟩,⟨172,(1),[4,8,12,16],[10],1292⟩,⟨172,(2),[4,8,12,16],[10],1293⟩,⟨172,(3),[4,8,12,16],[10],1294⟩,⟨172,(4),[4,8,12,16],[10],1295⟩,⟨172,(5),[4,8,12,16],[10],1292⟩,⟨172,(6),[4,8,12,16],[10],1293⟩,⟨172,(7),[4,8,12,16],[10],1294⟩,⟨172,(8),[4,8,12,16],[10],1291⟩,⟨172,(9),[4,8,12,16],[10],1292⟩,⟨172,(10),[4,8,12,16],[10],1293⟩,⟨172,(11),[4,8,12,16],[10],1294⟩,⟨172,(12),[4,8,12,16],[10],1296⟩,⟨172,(13),[4,8,12,16],[10],1292⟩,⟨172,(14),[4,8,12,16],[10],1293⟩,⟨172,(15),[4,8,12,16],[10],1294⟩,⟨175,(0),[3,4,8,12,15,16],[10],654⟩,⟨175,(1),[3,4,8,12,15,16],[10],655⟩,⟨175,(2),[3,4,8,12,15,16],[10],656⟩,⟨175,(3),[3,4,8,12,15,16],[10],657⟩,⟨175,(4),[3,4,8,12,15,16],[10],654⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1056
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1057
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1058
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1059
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1060
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1061
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1062
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1063
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1064
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1065
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1066
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1067
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1068
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1069
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1070
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1071
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1072
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1073
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1074
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1075
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1076
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1077
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1078
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1079
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1080
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1081
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1082
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1083
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1084
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1085
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1086
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1087
end Section14Records_12_1056_1088

#print axioms solution
