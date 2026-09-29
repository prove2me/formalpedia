-- Prove2me | solution 1 for Freiman.section14_s0003_records_2400_2432
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T13:43:30.506632+00:00
-- url     : https://prove2.me/submissions/a92a94e1-5f9a-415a-9161-3b7a53d09497

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
namespace Section14Records_3_2400_2432
private theorem valid2400 : RecordDataValid section14Catalog 3 (⟨438,(16),[3,7,15],[10],1132⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1132,[3,7,11,15],1136⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2401 : RecordDataValid section14Catalog 3 (⟨438,(17),[3,7,15],[10],1128⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1128,[3,7,11,15],1132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2402 : RecordDataValid section14Catalog 3 (⟨438,(18),[3,7,15],[10],1129⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1129,[3,7,11,15],1133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2403 : RecordDataValid section14Catalog 3 (⟨438,(19),[3,7,15],[10],1130⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1130,[3,7,11,15],1134⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2404 : RecordDataValid section14Catalog 3 (⟨438,(20),[3,7,15],[10],1133⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1133,[3,7,11,15],1137⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2405 : RecordDataValid section14Catalog 3 (⟨438,(21),[3,7,15],[10],1133⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1133,[3,7,11,15],1137⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2406 : RecordDataValid section14Catalog 3 (⟨438,(22),[3,7,15],[10],1133⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1133,[3,7,11,15],1137⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2407 : RecordDataValid section14Catalog 3 (⟨438,(23),[3,7,15],[10],1129⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1129,[3,7,11,15],1133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2408 : RecordDataValid section14Catalog 3 (⟨438,(24),[3,7,15],[10],1130⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1130,[3,7,11,15],1134⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2409 : RecordDataValid section14Catalog 3 (⟨441,(0),[3,7,15],[10],1134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1134,[3,5,7,8,9,11,12,15],1138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2410 : RecordDataValid section14Catalog 3 (⟨441,(1),[3,7,15],[10],1135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1135,[3,5,7,8,9,11,12,15],1139⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2411 : RecordDataValid section14Catalog 3 (⟨441,(2),[3,7,15],[10],1136⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1136,[3,5,7,8,9,11,12,15],1140⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2412 : RecordDataValid section14Catalog 3 (⟨441,(3),[3,7,15],[10],1136⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1136,[3,5,7,8,9,11,12,15],1140⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2413 : RecordDataValid section14Catalog 3 (⟨441,(4),[3,7,15],[10],1136⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1136,[3,5,7,8,9,11,12,15],1140⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2414 : RecordDataValid section14Catalog 3 (⟨441,(5),[3,7,15],[10],1134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1134,[3,5,7,8,9,11,12,15],1138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2415 : RecordDataValid section14Catalog 3 (⟨441,(6),[3,7,15],[10],1135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1135,[3,5,7,8,9,11,12,15],1139⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2416 : RecordDataValid section14Catalog 3 (⟨441,(7),[3,7,15],[10],1137⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1137,[3,5,7,8,9,11,12,15],1141⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2417 : RecordDataValid section14Catalog 3 (⟨441,(8),[3,7,15],[10],1138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1138,[3,5,7,8,9,11,12,15],1142⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2418 : RecordDataValid section14Catalog 3 (⟨441,(9),[3,7,15],[10],1137⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1137,[3,5,7,8,9,11,12,15],1141⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2419 : RecordDataValid section14Catalog 3 (⟨441,(10),[3,7,15],[10],1134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1134,[3,5,7,8,9,11,12,15],1138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2420 : RecordDataValid section14Catalog 3 (⟨441,(11),[3,7,15],[10],1135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1135,[3,5,7,8,9,11,12,15],1139⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2421 : RecordDataValid section14Catalog 3 (⟨441,(12),[3,7,15],[10],1139⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1139,[3,5,7,8,9,11,12,15],1143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2422 : RecordDataValid section14Catalog 3 (⟨441,(13),[3,7,15],[10],1138⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1138,[3,5,7,8,9,11,12,15],1142⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2423 : RecordDataValid section14Catalog 3 (⟨441,(14),[3,7,15],[10],1139⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1139,[3,5,7,8,9,11,12,15],1143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2424 : RecordDataValid section14Catalog 3 (⟨441,(15),[3,7,15],[10],1140⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1140,[3,5,7,8,9,11,12,15],1144⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2425 : RecordDataValid section14Catalog 3 (⟨441,(16),[3,7,15],[10],1141⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1141,[3,5,7,8,9,11,12,15],1145⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2426 : RecordDataValid section14Catalog 3 (⟨441,(17),[3,7,15],[10],1142⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1142,[3,5,7,8,9,11,12,15],1146⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2427 : RecordDataValid section14Catalog 3 (⟨441,(18),[3,7,15],[10],1143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1143,[3,5,7,8,9,11,12,15],1147⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2428 : RecordDataValid section14Catalog 3 (⟨441,(19),[3,7,15],[10],1142⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1142,[3,5,7,8,9,11,12,15],1146⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2429 : RecordDataValid section14Catalog 3 (⟨441,(20),[3,7,15],[10],1134⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1134,[3,5,7,8,9,11,12,15],1138⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2430 : RecordDataValid section14Catalog 3 (⟨441,(21),[3,7,15],[10],1135⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1135,[3,5,7,8,9,11,12,15],1139⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2431 : RecordDataValid section14Catalog 3 (⟨441,(22),[3,7,15],[10],1144⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1144,[3,5,7,8,9,11,12,15],1148⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 2400).take 32, section14RecordValid section14Catalog 3 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 2400).take 32 = [⟨438,(16),[3,7,15],[10],1132⟩,⟨438,(17),[3,7,15],[10],1128⟩,⟨438,(18),[3,7,15],[10],1129⟩,⟨438,(19),[3,7,15],[10],1130⟩,⟨438,(20),[3,7,15],[10],1133⟩,⟨438,(21),[3,7,15],[10],1133⟩,⟨438,(22),[3,7,15],[10],1133⟩,⟨438,(23),[3,7,15],[10],1129⟩,⟨438,(24),[3,7,15],[10],1130⟩,⟨441,(0),[3,7,15],[10],1134⟩,⟨441,(1),[3,7,15],[10],1135⟩,⟨441,(2),[3,7,15],[10],1136⟩,⟨441,(3),[3,7,15],[10],1136⟩,⟨441,(4),[3,7,15],[10],1136⟩,⟨441,(5),[3,7,15],[10],1134⟩,⟨441,(6),[3,7,15],[10],1135⟩,⟨441,(7),[3,7,15],[10],1137⟩,⟨441,(8),[3,7,15],[10],1138⟩,⟨441,(9),[3,7,15],[10],1137⟩,⟨441,(10),[3,7,15],[10],1134⟩,⟨441,(11),[3,7,15],[10],1135⟩,⟨441,(12),[3,7,15],[10],1139⟩,⟨441,(13),[3,7,15],[10],1138⟩,⟨441,(14),[3,7,15],[10],1139⟩,⟨441,(15),[3,7,15],[10],1140⟩,⟨441,(16),[3,7,15],[10],1141⟩,⟨441,(17),[3,7,15],[10],1142⟩,⟨441,(18),[3,7,15],[10],1143⟩,⟨441,(19),[3,7,15],[10],1142⟩,⟨441,(20),[3,7,15],[10],1134⟩,⟨441,(21),[3,7,15],[10],1135⟩,⟨441,(22),[3,7,15],[10],1144⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2400
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2401
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2402
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2403
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2404
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2405
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2406
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2407
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2408
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2409
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2410
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2411
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2412
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2413
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2414
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2415
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2416
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2417
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2418
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2419
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2420
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2421
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2422
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2423
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2424
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2425
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2426
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2427
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2428
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2429
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2430
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2431
end Section14Records_3_2400_2432

#print axioms solution
