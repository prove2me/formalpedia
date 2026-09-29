-- Prove2me | solution 1 for Freiman.section14_s0007_records_1216_1248
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T09:56:01.254337+00:00
-- url     : https://prove2.me/submissions/ad9851c4-c9ec-46cf-afb6-d046d8aa67e5

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
namespace Section14Records_7_1216_1248
private theorem valid1216 : RecordDataValid section14Catalog 7 (⟨202,(24),[3,7,15],[10],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1217 : RecordDataValid section14Catalog 7 (⟨205,(0),[3,7],[11],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1218 : RecordDataValid section14Catalog 7 (⟨205,(0),[7],[10],1600⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1600,[7],1605⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1219 : RecordDataValid section14Catalog 7 (⟨205,(1),[3,7],[11],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1220 : RecordDataValid section14Catalog 7 (⟨205,(1),[7],[10],1600⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1600,[7],1605⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1221 : RecordDataValid section14Catalog 7 (⟨205,(2),[3,7],[11],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1222 : RecordDataValid section14Catalog 7 (⟨205,(2),[7],[10],1600⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1600,[7],1605⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1223 : RecordDataValid section14Catalog 7 (⟨205,(3),[3,4,7,8,12,15,16],[10],712⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨712,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],713⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1224 : RecordDataValid section14Catalog 7 (⟨205,(3),[3,7],[11],712⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨712,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],713⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1225 : RecordDataValid section14Catalog 7 (⟨205,(4),[3,7],[11],711⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1226 : RecordDataValid section14Catalog 7 (⟨205,(4),[7],[10],1600⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1600,[7],1605⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1227 : RecordDataValid section14Catalog 7 (⟨205,(5),[3,7],[11],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1228 : RecordDataValid section14Catalog 7 (⟨205,(5),[7],[10],1601⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1601,[7],1606⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1229 : RecordDataValid section14Catalog 7 (⟨205,(6),[3,7],[11],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1230 : RecordDataValid section14Catalog 7 (⟨205,(6),[7],[10],1601⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1601,[7],1606⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1231 : RecordDataValid section14Catalog 7 (⟨205,(7),[3,7],[11],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1232 : RecordDataValid section14Catalog 7 (⟨205,(7),[7],[10],1601⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1601,[7],1606⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1233 : RecordDataValid section14Catalog 7 (⟨205,(8),[3,4,7,8,12,15,16],[10],714⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨714,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],715⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1234 : RecordDataValid section14Catalog 7 (⟨205,(8),[3,7],[11],714⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨714,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],715⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1235 : RecordDataValid section14Catalog 7 (⟨205,(9),[3,7],[11],713⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1236 : RecordDataValid section14Catalog 7 (⟨205,(9),[7],[10],1601⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1601,[7],1606⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1237 : RecordDataValid section14Catalog 7 (⟨205,(10),[3,7],[11],715⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨715,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],716⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1238 : RecordDataValid section14Catalog 7 (⟨205,(10),[7],[10],1602⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1602,[7],1607⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1239 : RecordDataValid section14Catalog 7 (⟨205,(11),[3,7],[11],716⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨716,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],717⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1240 : RecordDataValid section14Catalog 7 (⟨205,(11),[7],[10],1603⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1603,[7],1608⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1241 : RecordDataValid section14Catalog 7 (⟨205,(12),[3,7],[11],717⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨717,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],718⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1242 : RecordDataValid section14Catalog 7 (⟨205,(12),[7],[10],1604⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1604,[7],1609⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1243 : RecordDataValid section14Catalog 7 (⟨205,(13),[3,4,7,8,12,15,16],[10],718⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨718,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],719⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1244 : RecordDataValid section14Catalog 7 (⟨205,(13),[3,7],[11],718⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨718,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],719⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1245 : RecordDataValid section14Catalog 7 (⟨205,(14),[3,7],[11],719⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨719,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],720⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1246 : RecordDataValid section14Catalog 7 (⟨205,(14),[7],[10],1605⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1605,[7],1610⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1247 : RecordDataValid section14Catalog 7 (⟨205,(15),[3,7],[11],715⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨715,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],716⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 1216).take 32, section14RecordValid section14Catalog 7 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 1216).take 32 = [⟨202,(24),[3,7,15],[10],473⟩,⟨205,(0),[3,7],[11],711⟩,⟨205,(0),[7],[10],1600⟩,⟨205,(1),[3,7],[11],711⟩,⟨205,(1),[7],[10],1600⟩,⟨205,(2),[3,7],[11],711⟩,⟨205,(2),[7],[10],1600⟩,⟨205,(3),[3,4,7,8,12,15,16],[10],712⟩,⟨205,(3),[3,7],[11],712⟩,⟨205,(4),[3,7],[11],711⟩,⟨205,(4),[7],[10],1600⟩,⟨205,(5),[3,7],[11],713⟩,⟨205,(5),[7],[10],1601⟩,⟨205,(6),[3,7],[11],713⟩,⟨205,(6),[7],[10],1601⟩,⟨205,(7),[3,7],[11],713⟩,⟨205,(7),[7],[10],1601⟩,⟨205,(8),[3,4,7,8,12,15,16],[10],714⟩,⟨205,(8),[3,7],[11],714⟩,⟨205,(9),[3,7],[11],713⟩,⟨205,(9),[7],[10],1601⟩,⟨205,(10),[3,7],[11],715⟩,⟨205,(10),[7],[10],1602⟩,⟨205,(11),[3,7],[11],716⟩,⟨205,(11),[7],[10],1603⟩,⟨205,(12),[3,7],[11],717⟩,⟨205,(12),[7],[10],1604⟩,⟨205,(13),[3,4,7,8,12,15,16],[10],718⟩,⟨205,(13),[3,7],[11],718⟩,⟨205,(14),[3,7],[11],719⟩,⟨205,(14),[7],[10],1605⟩,⟨205,(15),[3,7],[11],715⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1216
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1217
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1218
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1219
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1220
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1221
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1222
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1223
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1224
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1225
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1226
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1227
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1228
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1229
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1230
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1231
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1232
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1233
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1234
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1235
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1236
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1237
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1238
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1239
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1240
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1241
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1242
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1243
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1244
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1245
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1246
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1247
end Section14Records_7_1216_1248

#print axioms solution
