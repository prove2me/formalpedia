-- Prove2me | solution 1 for Freiman.section14_s0016_records_1120_1152
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T23:19:44.2434+00:00
-- url     : https://prove2.me/submissions/9ed6562d-6b34-4ffa-94cf-5a53def758ff

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
namespace Section14Records_16_1120_1152
private theorem valid1120 : RecordDataValid section14Catalog 16 (⟨192,(3),[4,8,12,16],[10],1317⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1317,[4,8,9,12,16],1321⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1121 : RecordDataValid section14Catalog 16 (⟨192,(4),[4,8,12,16],[10],1318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1318,[4,8,9,12,16],1322⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1122 : RecordDataValid section14Catalog 16 (⟨192,(5),[4,8,12,16],[10],1315⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1315,[4,8,9,12,16],1319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1123 : RecordDataValid section14Catalog 16 (⟨192,(6),[4,8,12,16],[10],1316⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1316,[4,8,9,12,16],1320⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1124 : RecordDataValid section14Catalog 16 (⟨192,(7),[4,8,12,16],[10],1315⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1315,[4,8,9,12,16],1319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1125 : RecordDataValid section14Catalog 16 (⟨192,(8),[4,8,12,16],[10],1317⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1317,[4,8,9,12,16],1321⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1126 : RecordDataValid section14Catalog 16 (⟨192,(9),[4,8,12,16],[10],1318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1318,[4,8,9,12,16],1322⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1127 : RecordDataValid section14Catalog 16 (⟨192,(10),[4,8,12,16],[10],1319⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1319,[4,8,9,12,16],1323⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1128 : RecordDataValid section14Catalog 16 (⟨192,(11),[4,8,12,16],[10],1319⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1319,[4,8,9,12,16],1323⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1129 : RecordDataValid section14Catalog 16 (⟨192,(12),[4,8,12,16],[10],1319⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1319,[4,8,9,12,16],1323⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1130 : RecordDataValid section14Catalog 16 (⟨192,(13),[4,8,12,16],[10],1319⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1319,[4,8,9,12,16],1323⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1131 : RecordDataValid section14Catalog 16 (⟨192,(14),[4,8,12,16],[10],1318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1318,[4,8,9,12,16],1322⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1132 : RecordDataValid section14Catalog 16 (⟨192,(15),[4,8,12,16],[10],1320⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1320,[4,8,9,12,16],1324⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1133 : RecordDataValid section14Catalog 16 (⟨192,(16),[4,8,12,16],[10],1320⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1320,[4,8,9,12,16],1324⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1134 : RecordDataValid section14Catalog 16 (⟨192,(17),[4,8,12,16],[10],1320⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1320,[4,8,9,12,16],1324⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1135 : RecordDataValid section14Catalog 16 (⟨192,(18),[4,8,12,16],[10],1320⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1320,[4,8,9,12,16],1324⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1136 : RecordDataValid section14Catalog 16 (⟨192,(19),[4,8,12,16],[10],1320⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1320,[4,8,9,12,16],1324⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1137 : RecordDataValid section14Catalog 16 (⟨192,(20),[4,8,12,16],[10],1321⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1321,[4,8,9,12,16],1325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1138 : RecordDataValid section14Catalog 16 (⟨192,(21),[4,8,12,16],[10],1321⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1321,[4,8,9,12,16],1325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1139 : RecordDataValid section14Catalog 16 (⟨192,(22),[4,8,12,16],[10],1321⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1321,[4,8,9,12,16],1325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1140 : RecordDataValid section14Catalog 16 (⟨192,(23),[4,8,12,16],[10],1321⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1321,[4,8,9,12,16],1325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1141 : RecordDataValid section14Catalog 16 (⟨192,(24),[4,8,12,16],[10],1321⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1321,[4,8,9,12,16],1325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1142 : RecordDataValid section14Catalog 16 (⟨195,(0),[3,4,8,12,15,16],[10],697⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨697,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],698⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1143 : RecordDataValid section14Catalog 16 (⟨195,(1),[3,4,8,12,15,16],[10],697⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨697,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],698⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1144 : RecordDataValid section14Catalog 16 (⟨195,(2),[3,4,8,12,15,16],[10],698⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨698,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],699⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1145 : RecordDataValid section14Catalog 16 (⟨195,(3),[3,4,8,12,15,16],[10],698⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨698,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],699⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1146 : RecordDataValid section14Catalog 16 (⟨195,(4),[3,4,8,12,15,16],[10],699⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨699,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],700⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1147 : RecordDataValid section14Catalog 16 (⟨195,(5),[3,4,8,12,15,16],[10],700⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨700,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],701⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1148 : RecordDataValid section14Catalog 16 (⟨195,(6),[3,4,8,12,15,16],[10],699⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨699,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],700⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1149 : RecordDataValid section14Catalog 16 (⟨195,(7),[3,4,8,12,15,16],[10],701⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨701,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],702⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1150 : RecordDataValid section14Catalog 16 (⟨195,(8),[3,4,7,15,16],[10],702⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨702,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],703⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1151 : RecordDataValid section14Catalog 16 (⟨195,(9),[3,4,7,15,16],[10],703⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨703,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],704⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1120).take 32, section14RecordValid section14Catalog 16 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 1120).take 32 = [⟨192,(3),[4,8,12,16],[10],1317⟩,⟨192,(4),[4,8,12,16],[10],1318⟩,⟨192,(5),[4,8,12,16],[10],1315⟩,⟨192,(6),[4,8,12,16],[10],1316⟩,⟨192,(7),[4,8,12,16],[10],1315⟩,⟨192,(8),[4,8,12,16],[10],1317⟩,⟨192,(9),[4,8,12,16],[10],1318⟩,⟨192,(10),[4,8,12,16],[10],1319⟩,⟨192,(11),[4,8,12,16],[10],1319⟩,⟨192,(12),[4,8,12,16],[10],1319⟩,⟨192,(13),[4,8,12,16],[10],1319⟩,⟨192,(14),[4,8,12,16],[10],1318⟩,⟨192,(15),[4,8,12,16],[10],1320⟩,⟨192,(16),[4,8,12,16],[10],1320⟩,⟨192,(17),[4,8,12,16],[10],1320⟩,⟨192,(18),[4,8,12,16],[10],1320⟩,⟨192,(19),[4,8,12,16],[10],1320⟩,⟨192,(20),[4,8,12,16],[10],1321⟩,⟨192,(21),[4,8,12,16],[10],1321⟩,⟨192,(22),[4,8,12,16],[10],1321⟩,⟨192,(23),[4,8,12,16],[10],1321⟩,⟨192,(24),[4,8,12,16],[10],1321⟩,⟨195,(0),[3,4,8,12,15,16],[10],697⟩,⟨195,(1),[3,4,8,12,15,16],[10],697⟩,⟨195,(2),[3,4,8,12,15,16],[10],698⟩,⟨195,(3),[3,4,8,12,15,16],[10],698⟩,⟨195,(4),[3,4,8,12,15,16],[10],699⟩,⟨195,(5),[3,4,8,12,15,16],[10],700⟩,⟨195,(6),[3,4,8,12,15,16],[10],699⟩,⟨195,(7),[3,4,8,12,15,16],[10],701⟩,⟨195,(8),[3,4,7,15,16],[10],702⟩,⟨195,(9),[3,4,7,15,16],[10],703⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1120
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1121
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1122
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1123
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1124
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1125
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1126
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1127
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1128
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1129
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1130
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1131
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1132
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1133
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1134
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1135
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1136
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1137
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1138
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1139
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1140
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1141
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1142
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1143
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1144
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1145
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1146
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1147
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1148
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1149
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1150
  · exact recordValid_of_data section14Catalog 16 _ hnum valid1151
end Section14Records_16_1120_1152

#print axioms solution
