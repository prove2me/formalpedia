-- Prove2me | solution 1 for Freiman.section14_s0007_records_1088_1120
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T09:51:55.88197+00:00
-- url     : https://prove2.me/submissions/a59d4a77-be9d-4758-b5a7-dc0957252333

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
namespace Section14Records_7_1088_1120
private theorem valid1088 : RecordDataValid section14Catalog 7 (⟨197,(10),[3,7,15],[10],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1089 : RecordDataValid section14Catalog 7 (⟨197,(11),[3,7],[11],1012⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1012,[3,5,6,7],1016⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1090 : RecordDataValid section14Catalog 7 (⟨197,(11),[3,7,15],[10],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1091 : RecordDataValid section14Catalog 7 (⟨197,(12),[3,7],[11],1012⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1012,[3,5,6,7],1016⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1092 : RecordDataValid section14Catalog 7 (⟨197,(12),[3,7,15],[10],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1093 : RecordDataValid section14Catalog 7 (⟨197,(13),[3,7],[11],1012⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1012,[3,5,6,7],1016⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1094 : RecordDataValid section14Catalog 7 (⟨197,(13),[3,7,15],[10],457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1095 : RecordDataValid section14Catalog 7 (⟨197,(14),[3,7],[11],1011⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1011,[3,5,6,7],1015⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1096 : RecordDataValid section14Catalog 7 (⟨197,(14),[3,7,15],[10],456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨456,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1097 : RecordDataValid section14Catalog 7 (⟨197,(15),[3,7],[11],1013⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1013,[3,5,6,7],1017⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1098 : RecordDataValid section14Catalog 7 (⟨197,(15),[3,7,15],[10],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1099 : RecordDataValid section14Catalog 7 (⟨197,(16),[3,7],[11],1013⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1013,[3,5,6,7],1017⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1100 : RecordDataValid section14Catalog 7 (⟨197,(16),[3,7,15],[10],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1101 : RecordDataValid section14Catalog 7 (⟨197,(17),[3,7],[11],1013⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1013,[3,5,6,7],1017⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1102 : RecordDataValid section14Catalog 7 (⟨197,(17),[3,7,15],[10],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1103 : RecordDataValid section14Catalog 7 (⟨197,(18),[3,7],[11],1013⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1013,[3,5,6,7],1017⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1104 : RecordDataValid section14Catalog 7 (⟨197,(18),[3,7,15],[10],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1105 : RecordDataValid section14Catalog 7 (⟨197,(19),[3,7],[11],1013⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1013,[3,5,6,7],1017⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1106 : RecordDataValid section14Catalog 7 (⟨197,(19),[3,7,15],[10],458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1107 : RecordDataValid section14Catalog 7 (⟨197,(20),[3,7],[11],1014⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1014,[3,5,6,7],1018⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1108 : RecordDataValid section14Catalog 7 (⟨197,(20),[3,7,15],[10],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1109 : RecordDataValid section14Catalog 7 (⟨197,(21),[3,7],[11],1014⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1014,[3,5,6,7],1018⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1110 : RecordDataValid section14Catalog 7 (⟨197,(21),[3,7,15],[10],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1111 : RecordDataValid section14Catalog 7 (⟨197,(22),[3,7],[11],1014⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1014,[3,5,6,7],1018⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1112 : RecordDataValid section14Catalog 7 (⟨197,(22),[3,7,15],[10],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1113 : RecordDataValid section14Catalog 7 (⟨197,(23),[3,7],[11],1014⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1014,[3,5,6,7],1018⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1114 : RecordDataValid section14Catalog 7 (⟨197,(23),[3,7,15],[10],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1115 : RecordDataValid section14Catalog 7 (⟨197,(24),[3,7],[11],1014⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1014,[3,5,6,7],1018⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1116 : RecordDataValid section14Catalog 7 (⟨197,(24),[3,7,15],[10],459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1117 : RecordDataValid section14Catalog 7 (⟨200,(0),[3,7],[11],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1118 : RecordDataValid section14Catalog 7 (⟨200,(0),[7],[10],1593⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1593,[7],1598⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1119 : RecordDataValid section14Catalog 7 (⟨200,(1),[3,7],[11],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 1088).take 32, section14RecordValid section14Catalog 7 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 1088).take 32 = [⟨197,(10),[3,7,15],[10],457⟩,⟨197,(11),[3,7],[11],1012⟩,⟨197,(11),[3,7,15],[10],457⟩,⟨197,(12),[3,7],[11],1012⟩,⟨197,(12),[3,7,15],[10],457⟩,⟨197,(13),[3,7],[11],1012⟩,⟨197,(13),[3,7,15],[10],457⟩,⟨197,(14),[3,7],[11],1011⟩,⟨197,(14),[3,7,15],[10],456⟩,⟨197,(15),[3,7],[11],1013⟩,⟨197,(15),[3,7,15],[10],458⟩,⟨197,(16),[3,7],[11],1013⟩,⟨197,(16),[3,7,15],[10],458⟩,⟨197,(17),[3,7],[11],1013⟩,⟨197,(17),[3,7,15],[10],458⟩,⟨197,(18),[3,7],[11],1013⟩,⟨197,(18),[3,7,15],[10],458⟩,⟨197,(19),[3,7],[11],1013⟩,⟨197,(19),[3,7,15],[10],458⟩,⟨197,(20),[3,7],[11],1014⟩,⟨197,(20),[3,7,15],[10],459⟩,⟨197,(21),[3,7],[11],1014⟩,⟨197,(21),[3,7,15],[10],459⟩,⟨197,(22),[3,7],[11],1014⟩,⟨197,(22),[3,7,15],[10],459⟩,⟨197,(23),[3,7],[11],1014⟩,⟨197,(23),[3,7,15],[10],459⟩,⟨197,(24),[3,7],[11],1014⟩,⟨197,(24),[3,7,15],[10],459⟩,⟨200,(0),[3,7],[11],704⟩,⟨200,(0),[7],[10],1593⟩,⟨200,(1),[3,7],[11],704⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1088
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1089
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1090
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1091
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1092
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1093
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1094
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1095
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1096
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1097
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1098
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1099
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1100
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1101
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1102
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1103
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1104
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1105
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1106
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1107
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1108
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1109
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1110
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1111
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1112
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1113
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1114
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1115
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1116
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1117
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1118
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1119
end Section14Records_7_1088_1120

#print axioms solution
