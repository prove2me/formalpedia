-- Prove2me | solution 1 for Freiman.section14_s0015_records_1344_1376
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T19:21:04.12619+00:00
-- url     : https://prove2.me/submissions/ea754eec-7c5c-42b0-a4b3-0ca0fc664245

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
namespace Section14Records_15_1344_1376
private theorem valid1344 : RecordDataValid section14Catalog 15 (⟨426,(4),[3,7,15],[10],1100⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1100,[3,5,7,8,9,11,12,15],1104⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1345 : RecordDataValid section14Catalog 15 (⟨426,(5),[3,7,15],[10],1098⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1098,[3,5,7,8,9,11,12,15],1102⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1346 : RecordDataValid section14Catalog 15 (⟨426,(6),[3,7,15],[10],1099⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1099,[3,5,7,8,9,11,12,15],1103⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1347 : RecordDataValid section14Catalog 15 (⟨426,(7),[3,7,15],[10],1101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1101,[3,5,7,8,9,11,12,15],1105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1348 : RecordDataValid section14Catalog 15 (⟨426,(8),[3,7,15],[10],1102⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1102,[3,5,7,8,9,11,12,15],1106⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1349 : RecordDataValid section14Catalog 15 (⟨426,(9),[3,7,15],[10],1101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1101,[3,5,7,8,9,11,12,15],1105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1350 : RecordDataValid section14Catalog 15 (⟨428,(0),[3,7,15],[10],1103⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1103,[3,7,11,15],1107⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1351 : RecordDataValid section14Catalog 15 (⟨428,(1),[3,7,15],[10],1103⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1103,[3,7,11,15],1107⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1352 : RecordDataValid section14Catalog 15 (⟨428,(2),[3,7,15],[10],1104⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1104,[3,7,11,15],1108⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1353 : RecordDataValid section14Catalog 15 (⟨428,(3),[3,7,15],[10],1105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1105,[3,7,11,15],1109⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1354 : RecordDataValid section14Catalog 15 (⟨428,(4),[3,7,15],[10],1106⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1106,[3,7,11,15],1110⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1355 : RecordDataValid section14Catalog 15 (⟨428,(5),[3,7,15],[10],1107⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1107,[3,7,11,15],1111⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1356 : RecordDataValid section14Catalog 15 (⟨428,(6),[3,7,15],[10],1107⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1107,[3,7,11,15],1111⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1357 : RecordDataValid section14Catalog 15 (⟨428,(7),[3,7,15],[10],1107⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1107,[3,7,11,15],1111⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1358 : RecordDataValid section14Catalog 15 (⟨428,(8),[3,7,15],[10],1105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1105,[3,7,11,15],1109⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1359 : RecordDataValid section14Catalog 15 (⟨428,(9),[3,7,15],[10],1106⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1106,[3,7,11,15],1110⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1360 : RecordDataValid section14Catalog 15 (⟨431,(0),[3,7,15],[10],1108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1108,[3,5,7,8,9,11,12,15],1112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1361 : RecordDataValid section14Catalog 15 (⟨431,(1),[3,7,15],[10],1109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1109,[3,5,7,8,9,11,12,15],1113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1362 : RecordDataValid section14Catalog 15 (⟨431,(2),[3,7,15],[10],1110⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1110,[3,5,7,8,9,11,12,15],1114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1363 : RecordDataValid section14Catalog 15 (⟨431,(3),[3,7,15],[10],1110⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1110,[3,5,7,8,9,11,12,15],1114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1364 : RecordDataValid section14Catalog 15 (⟨431,(4),[3,7,15],[10],1110⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1110,[3,5,7,8,9,11,12,15],1114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1365 : RecordDataValid section14Catalog 15 (⟨431,(5),[3,7,15],[10],1108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1108,[3,5,7,8,9,11,12,15],1112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1366 : RecordDataValid section14Catalog 15 (⟨431,(6),[3,7,15],[10],1109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1109,[3,5,7,8,9,11,12,15],1113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1367 : RecordDataValid section14Catalog 15 (⟨431,(7),[3,7,15],[10],1111⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1111,[3,5,7,8,9,11,12,15],1115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1368 : RecordDataValid section14Catalog 15 (⟨431,(8),[3,7,15],[10],1112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1112,[3,5,7,8,9,11,12,15],1116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1369 : RecordDataValid section14Catalog 15 (⟨431,(9),[3,7,15],[10],1111⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1111,[3,5,7,8,9,11,12,15],1115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1370 : RecordDataValid section14Catalog 15 (⟨431,(10),[3,7,15],[10],1108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1108,[3,5,7,8,9,11,12,15],1112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1371 : RecordDataValid section14Catalog 15 (⟨431,(11),[3,7,15],[10],1109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1109,[3,5,7,8,9,11,12,15],1113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1372 : RecordDataValid section14Catalog 15 (⟨431,(12),[3,7,15],[10],1113⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1113,[3,5,7,8,9,11,12,15],1117⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1373 : RecordDataValid section14Catalog 15 (⟨431,(13),[3,7,15],[10],1112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1112,[3,5,7,8,9,11,12,15],1116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1374 : RecordDataValid section14Catalog 15 (⟨431,(14),[3,7,15],[10],1113⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1113,[3,5,7,8,9,11,12,15],1117⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1375 : RecordDataValid section14Catalog 15 (⟨431,(15),[3,7,15],[10],1108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1108,[3,5,7,8,9,11,12,15],1112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 1344).take 32, section14RecordValid section14Catalog 15 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 1344).take 32 = [⟨426,(4),[3,7,15],[10],1100⟩,⟨426,(5),[3,7,15],[10],1098⟩,⟨426,(6),[3,7,15],[10],1099⟩,⟨426,(7),[3,7,15],[10],1101⟩,⟨426,(8),[3,7,15],[10],1102⟩,⟨426,(9),[3,7,15],[10],1101⟩,⟨428,(0),[3,7,15],[10],1103⟩,⟨428,(1),[3,7,15],[10],1103⟩,⟨428,(2),[3,7,15],[10],1104⟩,⟨428,(3),[3,7,15],[10],1105⟩,⟨428,(4),[3,7,15],[10],1106⟩,⟨428,(5),[3,7,15],[10],1107⟩,⟨428,(6),[3,7,15],[10],1107⟩,⟨428,(7),[3,7,15],[10],1107⟩,⟨428,(8),[3,7,15],[10],1105⟩,⟨428,(9),[3,7,15],[10],1106⟩,⟨431,(0),[3,7,15],[10],1108⟩,⟨431,(1),[3,7,15],[10],1109⟩,⟨431,(2),[3,7,15],[10],1110⟩,⟨431,(3),[3,7,15],[10],1110⟩,⟨431,(4),[3,7,15],[10],1110⟩,⟨431,(5),[3,7,15],[10],1108⟩,⟨431,(6),[3,7,15],[10],1109⟩,⟨431,(7),[3,7,15],[10],1111⟩,⟨431,(8),[3,7,15],[10],1112⟩,⟨431,(9),[3,7,15],[10],1111⟩,⟨431,(10),[3,7,15],[10],1108⟩,⟨431,(11),[3,7,15],[10],1109⟩,⟨431,(12),[3,7,15],[10],1113⟩,⟨431,(13),[3,7,15],[10],1112⟩,⟨431,(14),[3,7,15],[10],1113⟩,⟨431,(15),[3,7,15],[10],1108⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1344
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1345
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1346
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1347
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1348
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1349
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1350
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1351
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1352
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1353
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1354
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1355
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1356
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1357
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1358
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1359
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1360
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1361
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1362
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1363
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1364
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1365
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1366
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1367
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1368
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1369
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1370
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1371
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1372
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1373
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1374
  · exact recordValid_of_data section14Catalog 15 _ hnum valid1375
end Section14Records_15_1344_1376

#print axioms solution
