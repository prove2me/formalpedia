-- Prove2me | solution 1 for Freiman.section14_s0009_records_2368_2400
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T21:26:37.705565+00:00
-- url     : https://prove2.me/submissions/0c363fa0-f477-4888-b68e-195f7f3e6a55

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
namespace Section14Records_9_2368_2400
private theorem valid2368 : RecordDataValid section14Catalog 9 (⟨247,(22),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2369 : RecordDataValid section14Catalog 9 (⟨247,(23),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2370 : RecordDataValid section14Catalog 9 (⟨247,(24),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2371 : RecordDataValid section14Catalog 9 (⟨253,(0),[9,10],[42],884⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨884,[1,2,4,5,6,8,9,10,12,13,14,16],886⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2372 : RecordDataValid section14Catalog 9 (⟨253,(1),[9,10],[42],894⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨894,[1,2,4,5,6,8,9,10,13,14,16],896⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2373 : RecordDataValid section14Catalog 9 (⟨253,(2),[9,10],[42],895⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨895,[1,2,3,4,5,6,7,8,9,10,13,14,16],897⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2374 : RecordDataValid section14Catalog 9 (⟨253,(3),[9,10],[42],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2375 : RecordDataValid section14Catalog 9 (⟨253,(4),[9,10],[42],30⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨30,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],30⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2376 : RecordDataValid section14Catalog 9 (⟨253,(5),[9,10],[42],884⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨884,[1,2,4,5,6,8,9,10,12,13,14,16],886⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2377 : RecordDataValid section14Catalog 9 (⟨253,(6),[9,10],[42],894⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨894,[1,2,4,5,6,8,9,10,13,14,16],896⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2378 : RecordDataValid section14Catalog 9 (⟨253,(7),[9],[42],1647⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1647,[8,9,12],1652⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2379 : RecordDataValid section14Catalog 9 (⟨253,(8),[9,10],[42],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2380 : RecordDataValid section14Catalog 9 (⟨253,(9),[9,10],[42],32⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨32,[1,2,4,5,6,8,9,10,12,13,14,16],32⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2381 : RecordDataValid section14Catalog 9 (⟨253,(10),[9,10],[42],84⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2382 : RecordDataValid section14Catalog 9 (⟨253,(11),[9,10],[42],897⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨897,[1,2,4,5,6,8,9,10,12,13,14,16],899⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2383 : RecordDataValid section14Catalog 9 (⟨253,(12),[9,10],[42],898⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨898,[1,2,4,5,6,8,9,10,12,13,14,16],900⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2384 : RecordDataValid section14Catalog 9 (⟨253,(13),[9,10],[42],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2385 : RecordDataValid section14Catalog 9 (⟨253,(14),[9,10],[42],34⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨34,[1,2,4,5,6,8,9,10,12,13,14,16],34⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2386 : RecordDataValid section14Catalog 9 (⟨253,(15),[9,10],[42],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2387 : RecordDataValid section14Catalog 9 (⟨253,(16),[9,10],[42],36⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨36,[1,2,4,5,6,8,9,10,12,13,14,16],36⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2388 : RecordDataValid section14Catalog 9 (⟨253,(17),[9,10],[42],37⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨37,[1,2,4,5,6,8,9,10,12,13,14,16],37⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2389 : RecordDataValid section14Catalog 9 (⟨253,(18),[9,10],[42],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2390 : RecordDataValid section14Catalog 9 (⟨253,(19),[9,10],[42],37⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨37,[1,2,4,5,6,8,9,10,12,13,14,16],37⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2391 : RecordDataValid section14Catalog 9 (⟨253,(20),[9,10],[42],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2392 : RecordDataValid section14Catalog 9 (⟨253,(21),[9,10],[42],39⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨39,[1,2,4,5,6,8,9,10,12,13,14,16],39⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2393 : RecordDataValid section14Catalog 9 (⟨253,(22),[9,10],[42],40⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨40,[1,2,4,5,6,8,9,10,12,13,14,16],40⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2394 : RecordDataValid section14Catalog 9 (⟨253,(23),[9,10],[42],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2395 : RecordDataValid section14Catalog 9 (⟨253,(24),[9,10],[42],40⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨40,[1,2,4,5,6,8,9,10,12,13,14,16],40⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2396 : RecordDataValid section14Catalog 9 (⟨259,(1),[9,10],[42],906⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨906,[1,2,4,5,6,8,9,10,12],908⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2397 : RecordDataValid section14Catalog 9 (⟨259,(3),[9,10],[42],907⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨907,[1,2,4,5,6,8,9,10,12],909⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2398 : RecordDataValid section14Catalog 9 (⟨259,(5),[9,10],[42],51⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨51,[1,2,4,9,10],51⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2399 : RecordDataValid section14Catalog 9 (⟨259,(7),[9],[42],52⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨52,[1,2,4,9,12],52⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2368).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2368).take 32 = [⟨247,(22),[9,10],[42],3⟩,⟨247,(23),[9,10],[42],3⟩,⟨247,(24),[9,10],[42],3⟩,⟨253,(0),[9,10],[42],884⟩,⟨253,(1),[9,10],[42],894⟩,⟨253,(2),[9,10],[42],895⟩,⟨253,(3),[9,10],[42],29⟩,⟨253,(4),[9,10],[42],30⟩,⟨253,(5),[9,10],[42],884⟩,⟨253,(6),[9,10],[42],894⟩,⟨253,(7),[9],[42],1647⟩,⟨253,(8),[9,10],[42],29⟩,⟨253,(9),[9,10],[42],32⟩,⟨253,(10),[9,10],[42],84⟩,⟨253,(11),[9,10],[42],897⟩,⟨253,(12),[9,10],[42],898⟩,⟨253,(13),[9,10],[42],29⟩,⟨253,(14),[9,10],[42],34⟩,⟨253,(15),[9,10],[42],35⟩,⟨253,(16),[9,10],[42],36⟩,⟨253,(17),[9,10],[42],37⟩,⟨253,(18),[9,10],[42],29⟩,⟨253,(19),[9,10],[42],37⟩,⟨253,(20),[9,10],[42],38⟩,⟨253,(21),[9,10],[42],39⟩,⟨253,(22),[9,10],[42],40⟩,⟨253,(23),[9,10],[42],29⟩,⟨253,(24),[9,10],[42],40⟩,⟨259,(1),[9,10],[42],906⟩,⟨259,(3),[9,10],[42],907⟩,⟨259,(5),[9,10],[42],51⟩,⟨259,(7),[9],[42],52⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2368
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2369
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2370
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2371
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2372
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2373
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2374
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2375
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2376
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2377
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2378
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2379
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2380
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2381
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2382
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2383
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2384
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2385
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2386
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2387
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2388
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2389
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2390
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2391
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2392
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2393
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2394
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2395
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2396
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2397
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2398
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2399
end Section14Records_9_2368_2400

#print axioms solution
