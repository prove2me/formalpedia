-- Prove2me | solution 1 for Freiman.section14_s0007_records_1376_1408
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T10:02:24.487805+00:00
-- url     : https://prove2.me/submissions/8db0cf25-8124-4421-8fe9-704e4cc9d7f8

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
namespace Section14Records_7_1376_1408
private theorem valid1376 : RecordDataValid section14Catalog 7 (⟨221,(9),[3,7,15],[10],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1377 : RecordDataValid section14Catalog 7 (⟨221,(10),[3,7],[11],1040⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1040,[3,5,6,7],1044⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1378 : RecordDataValid section14Catalog 7 (⟨221,(10),[3,7,15],[10],519⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨519,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],520⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1379 : RecordDataValid section14Catalog 7 (⟨221,(11),[3,7],[11],1040⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1040,[3,5,6,7],1044⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1380 : RecordDataValid section14Catalog 7 (⟨221,(11),[3,7,15],[10],519⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨519,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],520⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1381 : RecordDataValid section14Catalog 7 (⟨221,(12),[3,7],[11],1041⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1041,[3,5,6,7],1045⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1382 : RecordDataValid section14Catalog 7 (⟨221,(12),[3,7,15],[10],520⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨520,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],521⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1383 : RecordDataValid section14Catalog 7 (⟨221,(13),[3,7],[11],1038⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1038,[3,5,6,7],1042⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1384 : RecordDataValid section14Catalog 7 (⟨221,(13),[3,7,15],[10],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1385 : RecordDataValid section14Catalog 7 (⟨221,(14),[3,7],[11],1039⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1039,[3,5,6,7],1043⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1386 : RecordDataValid section14Catalog 7 (⟨221,(14),[3,7,15],[10],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1387 : RecordDataValid section14Catalog 7 (⟨221,(15),[3,7],[11],1042⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1042,[3,5,6,7],1046⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1388 : RecordDataValid section14Catalog 7 (⟨221,(15),[3,7,15],[10],521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨521,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],522⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1389 : RecordDataValid section14Catalog 7 (⟨221,(16),[3,7],[11],1042⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1042,[3,5,6,7],1046⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1390 : RecordDataValid section14Catalog 7 (⟨221,(16),[3,7,15],[10],521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨521,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],522⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1391 : RecordDataValid section14Catalog 7 (⟨221,(17),[3,7],[11],1042⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1042,[3,5,6,7],1046⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1392 : RecordDataValid section14Catalog 7 (⟨221,(17),[3,7,15],[10],521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨521,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],522⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1393 : RecordDataValid section14Catalog 7 (⟨221,(18),[3,7],[11],1038⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1038,[3,5,6,7],1042⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1394 : RecordDataValid section14Catalog 7 (⟨221,(18),[3,7,15],[10],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1395 : RecordDataValid section14Catalog 7 (⟨221,(19),[3,7],[11],1042⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1042,[3,5,6,7],1046⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1396 : RecordDataValid section14Catalog 7 (⟨221,(19),[3,7,15],[10],521⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨521,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],522⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1397 : RecordDataValid section14Catalog 7 (⟨221,(20),[3,7],[11],1043⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1043,[3,5,6,7],1047⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1398 : RecordDataValid section14Catalog 7 (⟨221,(20),[3,7,15],[10],522⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨522,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],523⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1399 : RecordDataValid section14Catalog 7 (⟨221,(21),[3,7],[11],1043⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1043,[3,5,6,7],1047⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1400 : RecordDataValid section14Catalog 7 (⟨221,(21),[3,7,15],[10],522⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨522,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],523⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1401 : RecordDataValid section14Catalog 7 (⟨221,(22),[3,7],[11],1043⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1043,[3,5,6,7],1047⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1402 : RecordDataValid section14Catalog 7 (⟨221,(22),[3,7,15],[10],522⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨522,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],523⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1403 : RecordDataValid section14Catalog 7 (⟨221,(23),[3,7],[11],1038⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1038,[3,5,6,7],1042⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1404 : RecordDataValid section14Catalog 7 (⟨221,(23),[3,7,15],[10],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1405 : RecordDataValid section14Catalog 7 (⟨221,(24),[3,7],[11],1039⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1039,[3,5,6,7],1043⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1406 : RecordDataValid section14Catalog 7 (⟨221,(24),[3,7,15],[10],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1407 : RecordDataValid section14Catalog 7 (⟨222,(0),[3,7],[11],735⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨735,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],736⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 1376).take 32, section14RecordValid section14Catalog 7 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (7 ∈ r.states))).drop 1376).take 32 = [⟨221,(9),[3,7,15],[10],518⟩,⟨221,(10),[3,7],[11],1040⟩,⟨221,(10),[3,7,15],[10],519⟩,⟨221,(11),[3,7],[11],1040⟩,⟨221,(11),[3,7,15],[10],519⟩,⟨221,(12),[3,7],[11],1041⟩,⟨221,(12),[3,7,15],[10],520⟩,⟨221,(13),[3,7],[11],1038⟩,⟨221,(13),[3,7,15],[10],517⟩,⟨221,(14),[3,7],[11],1039⟩,⟨221,(14),[3,7,15],[10],518⟩,⟨221,(15),[3,7],[11],1042⟩,⟨221,(15),[3,7,15],[10],521⟩,⟨221,(16),[3,7],[11],1042⟩,⟨221,(16),[3,7,15],[10],521⟩,⟨221,(17),[3,7],[11],1042⟩,⟨221,(17),[3,7,15],[10],521⟩,⟨221,(18),[3,7],[11],1038⟩,⟨221,(18),[3,7,15],[10],517⟩,⟨221,(19),[3,7],[11],1042⟩,⟨221,(19),[3,7,15],[10],521⟩,⟨221,(20),[3,7],[11],1043⟩,⟨221,(20),[3,7,15],[10],522⟩,⟨221,(21),[3,7],[11],1043⟩,⟨221,(21),[3,7,15],[10],522⟩,⟨221,(22),[3,7],[11],1043⟩,⟨221,(22),[3,7,15],[10],522⟩,⟨221,(23),[3,7],[11],1038⟩,⟨221,(23),[3,7,15],[10],517⟩,⟨221,(24),[3,7],[11],1039⟩,⟨221,(24),[3,7,15],[10],518⟩,⟨222,(0),[3,7],[11],735⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1376
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1377
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1378
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1379
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1380
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1381
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1382
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1383
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1384
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1385
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1386
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1387
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1388
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1389
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1390
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1391
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1392
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1393
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1394
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1395
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1396
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1397
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1398
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1399
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1400
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1401
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1402
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1403
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1404
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1405
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1406
  · exact recordValid_of_data section14Catalog 7 _ hnum valid1407
end Section14Records_7_1376_1408

#print axioms solution
