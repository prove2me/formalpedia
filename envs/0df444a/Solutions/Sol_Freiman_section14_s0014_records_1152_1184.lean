-- Prove2me | solution 1 for Freiman.section14_s0014_records_1152_1184
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T01:55:14.594985+00:00
-- url     : https://prove2.me/submissions/93806367-fc4e-41e7-82fb-7374c223d0a7

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
namespace Section14Records_14_1152_1184
private theorem valid1152 : RecordDataValid section14Catalog 14 (⟨167,(6),[1,2,5,6,13,14],[170],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1153 : RecordDataValid section14Catalog 14 (⟨167,(7),[1,2,5,6,13,14],[170],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1154 : RecordDataValid section14Catalog 14 (⟨167,(8),[1,2,5,6,13,14],[170],418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨418,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],419⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1155 : RecordDataValid section14Catalog 14 (⟨167,(9),[1,2,5,6,13,14],[170],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1156 : RecordDataValid section14Catalog 14 (⟨167,(10),[1,2,5,6,13,14],[170],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1157 : RecordDataValid section14Catalog 14 (⟨167,(11),[1,2,5,6,13,14],[170],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1158 : RecordDataValid section14Catalog 14 (⟨167,(12),[1,2,5,6,13,14],[170],423⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨423,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],424⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1159 : RecordDataValid section14Catalog 14 (⟨167,(13),[1,2,5,6,13,14],[170],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1160 : RecordDataValid section14Catalog 14 (⟨167,(14),[1,2,5,6,13,14],[170],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1161 : RecordDataValid section14Catalog 14 (⟨167,(15),[1,2,5,6,13,14],[170],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1162 : RecordDataValid section14Catalog 14 (⟨171,(0),[1,2,5,6,13,14],[170],650⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨650,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],651⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1163 : RecordDataValid section14Catalog 14 (⟨171,(1),[1,2,5,6,13,14],[170],651⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨651,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],652⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1164 : RecordDataValid section14Catalog 14 (⟨171,(2),[1,2,5,6,13,14],[170],652⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨652,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],653⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1165 : RecordDataValid section14Catalog 14 (⟨171,(3),[1,2,5,6,13,14],[170],653⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨653,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],654⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1166 : RecordDataValid section14Catalog 14 (⟨172,(0),[1,2,5,6,13,14],[170],428⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨428,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],429⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1167 : RecordDataValid section14Catalog 14 (⟨172,(1),[1,2,5,6,13,14],[170],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1168 : RecordDataValid section14Catalog 14 (⟨172,(2),[1,2,5,6,13,14],[170],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1169 : RecordDataValid section14Catalog 14 (⟨172,(3),[1,2,5,6,13,14],[170],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1170 : RecordDataValid section14Catalog 14 (⟨172,(4),[1,2,5,6,13,14],[170],432⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨432,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],433⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1171 : RecordDataValid section14Catalog 14 (⟨172,(5),[1,2,5,6,13,14],[170],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1172 : RecordDataValid section14Catalog 14 (⟨172,(6),[1,2,5,6,13,14],[170],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1173 : RecordDataValid section14Catalog 14 (⟨172,(7),[1,2,5,6,13,14],[170],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1174 : RecordDataValid section14Catalog 14 (⟨172,(8),[1,2,5,6,13,14],[170],428⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨428,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],429⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1175 : RecordDataValid section14Catalog 14 (⟨172,(9),[1,2,5,6,13,14],[170],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1176 : RecordDataValid section14Catalog 14 (⟨172,(10),[1,2,5,6,13,14],[170],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1177 : RecordDataValid section14Catalog 14 (⟨172,(11),[1,2,5,6,13,14],[170],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1178 : RecordDataValid section14Catalog 14 (⟨172,(12),[1,2,5,6,13,14],[170],433⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨433,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],434⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1179 : RecordDataValid section14Catalog 14 (⟨172,(13),[1,2,5,6,13,14],[170],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1180 : RecordDataValid section14Catalog 14 (⟨172,(14),[1,2,5,6,13,14],[170],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1181 : RecordDataValid section14Catalog 14 (⟨172,(15),[1,2,5,6,13,14],[170],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1182 : RecordDataValid section14Catalog 14 (⟨175,(0),[1,2,5,6,13,14],[170],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1183 : RecordDataValid section14Catalog 14 (⟨175,(1),[1,2,5,6,13,14],[170],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 1152).take 32, section14RecordValid section14Catalog 14 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (14 ∈ r.states))).drop 1152).take 32 = [⟨167,(6),[1,2,5,6,13,14],[170],420⟩,⟨167,(7),[1,2,5,6,13,14],[170],421⟩,⟨167,(8),[1,2,5,6,13,14],[170],418⟩,⟨167,(9),[1,2,5,6,13,14],[170],419⟩,⟨167,(10),[1,2,5,6,13,14],[170],420⟩,⟨167,(11),[1,2,5,6,13,14],[170],421⟩,⟨167,(12),[1,2,5,6,13,14],[170],423⟩,⟨167,(13),[1,2,5,6,13,14],[170],419⟩,⟨167,(14),[1,2,5,6,13,14],[170],420⟩,⟨167,(15),[1,2,5,6,13,14],[170],421⟩,⟨171,(0),[1,2,5,6,13,14],[170],650⟩,⟨171,(1),[1,2,5,6,13,14],[170],651⟩,⟨171,(2),[1,2,5,6,13,14],[170],652⟩,⟨171,(3),[1,2,5,6,13,14],[170],653⟩,⟨172,(0),[1,2,5,6,13,14],[170],428⟩,⟨172,(1),[1,2,5,6,13,14],[170],429⟩,⟨172,(2),[1,2,5,6,13,14],[170],430⟩,⟨172,(3),[1,2,5,6,13,14],[170],431⟩,⟨172,(4),[1,2,5,6,13,14],[170],432⟩,⟨172,(5),[1,2,5,6,13,14],[170],429⟩,⟨172,(6),[1,2,5,6,13,14],[170],430⟩,⟨172,(7),[1,2,5,6,13,14],[170],431⟩,⟨172,(8),[1,2,5,6,13,14],[170],428⟩,⟨172,(9),[1,2,5,6,13,14],[170],429⟩,⟨172,(10),[1,2,5,6,13,14],[170],430⟩,⟨172,(11),[1,2,5,6,13,14],[170],431⟩,⟨172,(12),[1,2,5,6,13,14],[170],433⟩,⟨172,(13),[1,2,5,6,13,14],[170],429⟩,⟨172,(14),[1,2,5,6,13,14],[170],430⟩,⟨172,(15),[1,2,5,6,13,14],[170],431⟩,⟨175,(0),[1,2,5,6,13,14],[170],654⟩,⟨175,(1),[1,2,5,6,13,14],[170],655⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1152
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1153
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1154
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1155
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1156
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1157
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1158
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1159
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1160
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1161
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1162
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1163
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1164
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1165
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1166
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1167
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1168
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1169
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1170
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1171
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1172
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1173
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1174
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1175
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1176
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1177
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1178
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1179
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1180
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1181
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1182
  · exact recordValid_of_data section14Catalog 14 _ hnum valid1183
end Section14Records_14_1152_1184

#print axioms solution
