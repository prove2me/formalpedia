-- Prove2me | solution 1 for Freiman.section14_s0012_records_1344_1376
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T04:53:54.454004+00:00
-- url     : https://prove2.me/submissions/4528cbbf-6c0d-4121-b758-9917522a7190

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
namespace Section14Records_12_1344_1376
private theorem valid1344 : RecordDataValid section14Catalog 12 (⟨207,(5),[4,8,12,16],[10],1336⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1336,[4,8,9,12,16],1340⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1345 : RecordDataValid section14Catalog 12 (⟨207,(6),[4,8,12,16],[10],1337⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1337,[4,8,9,12,16],1341⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1346 : RecordDataValid section14Catalog 12 (⟨207,(7),[4,8,12,16],[10],1336⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1336,[4,8,9,12,16],1340⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1347 : RecordDataValid section14Catalog 12 (⟨207,(8),[4,8,12,16],[10],1338⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1338,[4,8,9,12,16],1342⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1348 : RecordDataValid section14Catalog 12 (⟨207,(9),[4,8,12,16],[10],1339⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1339,[4,8,9,12,16],1343⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1349 : RecordDataValid section14Catalog 12 (⟨207,(10),[4,8,12,16],[10],1340⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1340,[4,8,9,12,16],1344⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1350 : RecordDataValid section14Catalog 12 (⟨207,(11),[4,8,12,16],[10],1340⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1340,[4,8,9,12,16],1344⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1351 : RecordDataValid section14Catalog 12 (⟨207,(12),[4,8,12,16],[10],1340⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1340,[4,8,9,12,16],1344⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1352 : RecordDataValid section14Catalog 12 (⟨207,(13),[4,8,12,16],[10],1340⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1340,[4,8,9,12,16],1344⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1353 : RecordDataValid section14Catalog 12 (⟨207,(14),[4,8,12,16],[10],1339⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1339,[4,8,9,12,16],1343⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1354 : RecordDataValid section14Catalog 12 (⟨207,(15),[4,8,12,16],[10],1341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1341,[4,8,9,12,16],1345⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1355 : RecordDataValid section14Catalog 12 (⟨207,(16),[4,8,12,16],[10],1341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1341,[4,8,9,12,16],1345⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1356 : RecordDataValid section14Catalog 12 (⟨207,(17),[4,8,12,16],[10],1341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1341,[4,8,9,12,16],1345⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1357 : RecordDataValid section14Catalog 12 (⟨207,(18),[4,8,12,16],[10],1341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1341,[4,8,9,12,16],1345⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1358 : RecordDataValid section14Catalog 12 (⟨207,(19),[4,8,12,16],[10],1341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1341,[4,8,9,12,16],1345⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1359 : RecordDataValid section14Catalog 12 (⟨207,(20),[4,8,12,16],[10],1342⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1342,[4,8,9,12,16],1346⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1360 : RecordDataValid section14Catalog 12 (⟨207,(21),[4,8,12,16],[10],1342⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1342,[4,8,9,12,16],1346⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1361 : RecordDataValid section14Catalog 12 (⟨207,(22),[4,8,12,16],[10],1342⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1342,[4,8,9,12,16],1346⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1362 : RecordDataValid section14Catalog 12 (⟨207,(23),[4,8,12,16],[10],1342⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1342,[4,8,9,12,16],1346⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1363 : RecordDataValid section14Catalog 12 (⟨207,(24),[4,8,12,16],[10],1342⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1342,[4,8,9,12,16],1346⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1364 : RecordDataValid section14Catalog 12 (⟨210,(0),[4,8,12,16],[10],722⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨722,[1,2,4,5,6,8,9,10,12,13,14,16],723⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1365 : RecordDataValid section14Catalog 12 (⟨210,(1),[4,8,12,16],[10],723⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨723,[1,2,4,5,6,8,9,10,12,13,14,16],724⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1366 : RecordDataValid section14Catalog 12 (⟨210,(2),[4,8,12,16],[10],724⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨724,[1,2,4,5,6,8,9,10,12,13,14,16],725⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1367 : RecordDataValid section14Catalog 12 (⟨210,(3),[4,8,12,16],[10],725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨725,[1,2,4,5,6,8,9,10,12,13,14,16],726⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1368 : RecordDataValid section14Catalog 12 (⟨210,(4),[4,8,12,16],[10],722⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨722,[1,2,4,5,6,8,9,10,12,13,14,16],723⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1369 : RecordDataValid section14Catalog 12 (⟨210,(5),[4,8,12,16],[10],723⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨723,[1,2,4,5,6,8,9,10,12,13,14,16],724⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1370 : RecordDataValid section14Catalog 12 (⟨210,(6),[4,8,12,16],[10],726⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨726,[1,2,4,5,6,8,9,10,12,13,14,16],727⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1371 : RecordDataValid section14Catalog 12 (⟨210,(7),[4,8,12,16],[10],725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨725,[1,2,4,5,6,8,9,10,12,13,14,16],726⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1372 : RecordDataValid section14Catalog 12 (⟨210,(8),[4,8,12,16],[10],722⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨722,[1,2,4,5,6,8,9,10,12,13,14,16],723⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1373 : RecordDataValid section14Catalog 12 (⟨210,(9),[4,8,12,16],[10],723⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨723,[1,2,4,5,6,8,9,10,12,13,14,16],724⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1374 : RecordDataValid section14Catalog 12 (⟨210,(10),[4,8,12,16],[10],724⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨724,[1,2,4,5,6,8,9,10,12,13,14,16],725⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1375 : RecordDataValid section14Catalog 12 (⟨210,(11),[4,8,12,16],[10],725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨725,[1,2,4,5,6,8,9,10,12,13,14,16],726⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1344).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 1344).take 32 = [⟨207,(5),[4,8,12,16],[10],1336⟩,⟨207,(6),[4,8,12,16],[10],1337⟩,⟨207,(7),[4,8,12,16],[10],1336⟩,⟨207,(8),[4,8,12,16],[10],1338⟩,⟨207,(9),[4,8,12,16],[10],1339⟩,⟨207,(10),[4,8,12,16],[10],1340⟩,⟨207,(11),[4,8,12,16],[10],1340⟩,⟨207,(12),[4,8,12,16],[10],1340⟩,⟨207,(13),[4,8,12,16],[10],1340⟩,⟨207,(14),[4,8,12,16],[10],1339⟩,⟨207,(15),[4,8,12,16],[10],1341⟩,⟨207,(16),[4,8,12,16],[10],1341⟩,⟨207,(17),[4,8,12,16],[10],1341⟩,⟨207,(18),[4,8,12,16],[10],1341⟩,⟨207,(19),[4,8,12,16],[10],1341⟩,⟨207,(20),[4,8,12,16],[10],1342⟩,⟨207,(21),[4,8,12,16],[10],1342⟩,⟨207,(22),[4,8,12,16],[10],1342⟩,⟨207,(23),[4,8,12,16],[10],1342⟩,⟨207,(24),[4,8,12,16],[10],1342⟩,⟨210,(0),[4,8,12,16],[10],722⟩,⟨210,(1),[4,8,12,16],[10],723⟩,⟨210,(2),[4,8,12,16],[10],724⟩,⟨210,(3),[4,8,12,16],[10],725⟩,⟨210,(4),[4,8,12,16],[10],722⟩,⟨210,(5),[4,8,12,16],[10],723⟩,⟨210,(6),[4,8,12,16],[10],726⟩,⟨210,(7),[4,8,12,16],[10],725⟩,⟨210,(8),[4,8,12,16],[10],722⟩,⟨210,(9),[4,8,12,16],[10],723⟩,⟨210,(10),[4,8,12,16],[10],724⟩,⟨210,(11),[4,8,12,16],[10],725⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1344
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1345
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1346
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1347
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1348
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1349
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1350
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1351
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1352
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1353
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1354
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1355
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1356
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1357
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1358
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1359
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1360
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1361
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1362
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1363
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1364
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1365
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1366
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1367
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1368
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1369
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1370
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1371
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1372
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1373
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1374
  · exact recordValid_of_data section14Catalog 12 _ hnum valid1375
end Section14Records_12_1344_1376

#print axioms solution
