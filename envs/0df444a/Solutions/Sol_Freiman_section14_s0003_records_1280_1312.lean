-- Prove2me | solution 1 for Freiman.section14_s0003_records_1280_1312
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T12:59:01.650345+00:00
-- url     : https://prove2.me/submissions/3d6cf453-f26f-492f-ba1d-66290ec84004

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
namespace Section14Records_3_1280_1312
private theorem valid1280 : RecordDataValid section14Catalog 3 (⟨207,(5),[3,7],[11],1022⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1022,[3,5,6,7],1026⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1281 : RecordDataValid section14Catalog 3 (⟨207,(5),[3,7,15],[10],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1282 : RecordDataValid section14Catalog 3 (⟨207,(6),[3,7],[11],1023⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1023,[3,5,6,7],1027⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1283 : RecordDataValid section14Catalog 3 (⟨207,(6),[3,7,15],[10],482⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨482,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],483⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1284 : RecordDataValid section14Catalog 3 (⟨207,(7),[3,7],[11],1022⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1022,[3,5,6,7],1026⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1285 : RecordDataValid section14Catalog 3 (⟨207,(7),[3,7,15],[10],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1286 : RecordDataValid section14Catalog 3 (⟨207,(8),[3,7],[11],1024⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1024,[3,5,6,7],1028⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1287 : RecordDataValid section14Catalog 3 (⟨207,(8),[3,7,15],[10],483⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨483,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],484⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1288 : RecordDataValid section14Catalog 3 (⟨207,(9),[3,7],[11],1025⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1025,[3,5,6,7],1029⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1289 : RecordDataValid section14Catalog 3 (⟨207,(9),[3,7,15],[10],484⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨484,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],485⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1290 : RecordDataValid section14Catalog 3 (⟨207,(10),[3,7],[11],1026⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1026,[3,5,6,7],1030⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1291 : RecordDataValid section14Catalog 3 (⟨207,(10),[3,7,15],[10],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1292 : RecordDataValid section14Catalog 3 (⟨207,(11),[3,7],[11],1026⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1026,[3,5,6,7],1030⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1293 : RecordDataValid section14Catalog 3 (⟨207,(11),[3,7,15],[10],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1294 : RecordDataValid section14Catalog 3 (⟨207,(12),[3,7],[11],1026⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1026,[3,5,6,7],1030⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1295 : RecordDataValid section14Catalog 3 (⟨207,(12),[3,7,15],[10],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1296 : RecordDataValid section14Catalog 3 (⟨207,(13),[3,7],[11],1026⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1026,[3,5,6,7],1030⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1297 : RecordDataValid section14Catalog 3 (⟨207,(13),[3,7,15],[10],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1298 : RecordDataValid section14Catalog 3 (⟨207,(14),[3,7],[11],1025⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1025,[3,5,6,7],1029⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1299 : RecordDataValid section14Catalog 3 (⟨207,(14),[3,7,15],[10],484⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨484,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],485⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1300 : RecordDataValid section14Catalog 3 (⟨207,(15),[3,7],[11],1027⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1027,[3,5,6,7],1031⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1301 : RecordDataValid section14Catalog 3 (⟨207,(15),[3,7,15],[10],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1302 : RecordDataValid section14Catalog 3 (⟨207,(16),[3,7],[11],1027⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1027,[3,5,6,7],1031⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1303 : RecordDataValid section14Catalog 3 (⟨207,(16),[3,7,15],[10],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1304 : RecordDataValid section14Catalog 3 (⟨207,(17),[3,7],[11],1027⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1027,[3,5,6,7],1031⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1305 : RecordDataValid section14Catalog 3 (⟨207,(17),[3,7,15],[10],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1306 : RecordDataValid section14Catalog 3 (⟨207,(18),[3,7],[11],1027⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1027,[3,5,6,7],1031⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1307 : RecordDataValid section14Catalog 3 (⟨207,(18),[3,7,15],[10],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1308 : RecordDataValid section14Catalog 3 (⟨207,(19),[3,7],[11],1027⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1027,[3,5,6,7],1031⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1309 : RecordDataValid section14Catalog 3 (⟨207,(19),[3,7,15],[10],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1310 : RecordDataValid section14Catalog 3 (⟨207,(20),[3,7],[11],1028⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1028,[3,5,6,7],1032⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1311 : RecordDataValid section14Catalog 3 (⟨207,(20),[3,7,15],[10],487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨487,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],488⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 1280).take 32, section14RecordValid section14Catalog 3 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 1280).take 32 = [⟨207,(5),[3,7],[11],1022⟩,⟨207,(5),[3,7,15],[10],481⟩,⟨207,(6),[3,7],[11],1023⟩,⟨207,(6),[3,7,15],[10],482⟩,⟨207,(7),[3,7],[11],1022⟩,⟨207,(7),[3,7,15],[10],481⟩,⟨207,(8),[3,7],[11],1024⟩,⟨207,(8),[3,7,15],[10],483⟩,⟨207,(9),[3,7],[11],1025⟩,⟨207,(9),[3,7,15],[10],484⟩,⟨207,(10),[3,7],[11],1026⟩,⟨207,(10),[3,7,15],[10],485⟩,⟨207,(11),[3,7],[11],1026⟩,⟨207,(11),[3,7,15],[10],485⟩,⟨207,(12),[3,7],[11],1026⟩,⟨207,(12),[3,7,15],[10],485⟩,⟨207,(13),[3,7],[11],1026⟩,⟨207,(13),[3,7,15],[10],485⟩,⟨207,(14),[3,7],[11],1025⟩,⟨207,(14),[3,7,15],[10],484⟩,⟨207,(15),[3,7],[11],1027⟩,⟨207,(15),[3,7,15],[10],486⟩,⟨207,(16),[3,7],[11],1027⟩,⟨207,(16),[3,7,15],[10],486⟩,⟨207,(17),[3,7],[11],1027⟩,⟨207,(17),[3,7,15],[10],486⟩,⟨207,(18),[3,7],[11],1027⟩,⟨207,(18),[3,7,15],[10],486⟩,⟨207,(19),[3,7],[11],1027⟩,⟨207,(19),[3,7,15],[10],486⟩,⟨207,(20),[3,7],[11],1028⟩,⟨207,(20),[3,7,15],[10],487⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1280
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1281
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1282
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1283
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1284
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1285
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1286
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1287
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1288
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1289
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1290
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1291
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1292
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1293
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1294
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1295
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1296
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1297
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1298
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1299
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1300
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1301
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1302
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1303
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1304
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1305
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1306
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1307
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1308
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1309
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1310
  · exact recordValid_of_data section14Catalog 3 _ hnum valid1311
end Section14Records_3_1280_1312

#print axioms solution
