-- Prove2me | solution 1 for Freiman.section14_s0003_records_2368_2400
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T13:42:07.582716+00:00
-- url     : https://prove2.me/submissions/7b46dc4d-ad69-4545-b1f7-23f239c96775

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
namespace Section14Records_3_2368_2400
private theorem valid2368 : RecordDataValid section14Catalog 3 (⟨433,(4),[3,7,15],[10],1118⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1118,[3,7,11,15],1122⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2369 : RecordDataValid section14Catalog 3 (⟨433,(5),[3,7,15],[10],1119⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1119,[3,7,11,15],1123⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2370 : RecordDataValid section14Catalog 3 (⟨433,(6),[3,7,15],[10],1119⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1119,[3,7,11,15],1123⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2371 : RecordDataValid section14Catalog 3 (⟨433,(7),[3,7,15],[10],1119⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1119,[3,7,11,15],1123⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2372 : RecordDataValid section14Catalog 3 (⟨433,(8),[3,7,15],[10],1117⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1117,[3,7,11,15],1121⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2373 : RecordDataValid section14Catalog 3 (⟨433,(9),[3,7,15],[10],1118⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1118,[3,7,11,15],1122⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2374 : RecordDataValid section14Catalog 3 (⟨436,(0),[3,7,15],[10],1120⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1120,[3,5,7,8,9,11,12,15],1124⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2375 : RecordDataValid section14Catalog 3 (⟨436,(1),[3,7,15],[10],1121⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1121,[3,5,7,8,9,11,12,15],1125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2376 : RecordDataValid section14Catalog 3 (⟨436,(2),[3,7,15],[10],1122⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1122,[3,5,7,8,9,11,12,15],1126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2377 : RecordDataValid section14Catalog 3 (⟨436,(3),[3,7,15],[10],1122⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1122,[3,5,7,8,9,11,12,15],1126⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2378 : RecordDataValid section14Catalog 3 (⟨436,(4),[3,7,15],[10],1123⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1123,[3,5,7,8,9,11,12,15],1127⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2379 : RecordDataValid section14Catalog 3 (⟨436,(5),[3,7,15],[10],1120⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1120,[3,5,7,8,9,11,12,15],1124⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2380 : RecordDataValid section14Catalog 3 (⟨436,(6),[3,7,15],[10],1121⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1121,[3,5,7,8,9,11,12,15],1125⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2381 : RecordDataValid section14Catalog 3 (⟨436,(7),[3,7,15],[10],1124⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1124,[3,5,7,8,9,11,12,15],1128⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2382 : RecordDataValid section14Catalog 3 (⟨436,(8),[3,7,15],[10],1125⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1125,[3,5,7,8,9,11,12,15],1129⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2383 : RecordDataValid section14Catalog 3 (⟨436,(9),[3,7,15],[10],1126⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1126,[3,5,7,8,9,11,12,15],1130⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2384 : RecordDataValid section14Catalog 3 (⟨438,(0),[3,7,15],[10],1127⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1127,[3,7,11,15],1131⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2385 : RecordDataValid section14Catalog 3 (⟨438,(1),[3,7,15],[10],1127⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1127,[3,7,11,15],1131⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2386 : RecordDataValid section14Catalog 3 (⟨438,(2),[3,7,15],[10],1128⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1128,[3,7,11,15],1132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2387 : RecordDataValid section14Catalog 3 (⟨438,(3),[3,7,15],[10],1129⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1129,[3,7,11,15],1133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2388 : RecordDataValid section14Catalog 3 (⟨438,(4),[3,7,15],[10],1130⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1130,[3,7,11,15],1134⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2389 : RecordDataValid section14Catalog 3 (⟨438,(5),[3,7,15],[10],1131⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1131,[3,7,11,15],1135⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2390 : RecordDataValid section14Catalog 3 (⟨438,(6),[3,7,15],[10],1131⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1131,[3,7,11,15],1135⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2391 : RecordDataValid section14Catalog 3 (⟨438,(7),[3,7,15],[10],1128⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1128,[3,7,11,15],1132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2392 : RecordDataValid section14Catalog 3 (⟨438,(8),[3,7,15],[10],1129⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1129,[3,7,11,15],1133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2393 : RecordDataValid section14Catalog 3 (⟨438,(9),[3,7,15],[10],1130⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1130,[3,7,11,15],1134⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2394 : RecordDataValid section14Catalog 3 (⟨438,(10),[3,7,15],[10],1127⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1127,[3,7,11,15],1131⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2395 : RecordDataValid section14Catalog 3 (⟨438,(11),[3,7,15],[10],1127⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1127,[3,7,11,15],1131⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2396 : RecordDataValid section14Catalog 3 (⟨438,(12),[3,7,15],[10],1128⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1128,[3,7,11,15],1132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2397 : RecordDataValid section14Catalog 3 (⟨438,(13),[3,7,15],[10],1129⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1129,[3,7,11,15],1133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2398 : RecordDataValid section14Catalog 3 (⟨438,(14),[3,7,15],[10],1130⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1130,[3,7,11,15],1134⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2399 : RecordDataValid section14Catalog 3 (⟨438,(15),[3,7,15],[10],1132⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1132,[3,7,11,15],1136⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 2368).take 32, section14RecordValid section14Catalog 3 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (3 ∈ r.states))).drop 2368).take 32 = [⟨433,(4),[3,7,15],[10],1118⟩,⟨433,(5),[3,7,15],[10],1119⟩,⟨433,(6),[3,7,15],[10],1119⟩,⟨433,(7),[3,7,15],[10],1119⟩,⟨433,(8),[3,7,15],[10],1117⟩,⟨433,(9),[3,7,15],[10],1118⟩,⟨436,(0),[3,7,15],[10],1120⟩,⟨436,(1),[3,7,15],[10],1121⟩,⟨436,(2),[3,7,15],[10],1122⟩,⟨436,(3),[3,7,15],[10],1122⟩,⟨436,(4),[3,7,15],[10],1123⟩,⟨436,(5),[3,7,15],[10],1120⟩,⟨436,(6),[3,7,15],[10],1121⟩,⟨436,(7),[3,7,15],[10],1124⟩,⟨436,(8),[3,7,15],[10],1125⟩,⟨436,(9),[3,7,15],[10],1126⟩,⟨438,(0),[3,7,15],[10],1127⟩,⟨438,(1),[3,7,15],[10],1127⟩,⟨438,(2),[3,7,15],[10],1128⟩,⟨438,(3),[3,7,15],[10],1129⟩,⟨438,(4),[3,7,15],[10],1130⟩,⟨438,(5),[3,7,15],[10],1131⟩,⟨438,(6),[3,7,15],[10],1131⟩,⟨438,(7),[3,7,15],[10],1128⟩,⟨438,(8),[3,7,15],[10],1129⟩,⟨438,(9),[3,7,15],[10],1130⟩,⟨438,(10),[3,7,15],[10],1127⟩,⟨438,(11),[3,7,15],[10],1127⟩,⟨438,(12),[3,7,15],[10],1128⟩,⟨438,(13),[3,7,15],[10],1129⟩,⟨438,(14),[3,7,15],[10],1130⟩,⟨438,(15),[3,7,15],[10],1132⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2368
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2369
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2370
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2371
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2372
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2373
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2374
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2375
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2376
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2377
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2378
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2379
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2380
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2381
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2382
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2383
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2384
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2385
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2386
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2387
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2388
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2389
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2390
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2391
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2392
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2393
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2394
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2395
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2396
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2397
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2398
  · exact recordValid_of_data section14Catalog 3 _ hnum valid2399
end Section14Records_3_2368_2400

#print axioms solution
