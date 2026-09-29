-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_2368_2432
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:14:21.627204+00:00
-- url     : https://prove2.me/submissions/54d48224-9d74-449e-a186-23623829dfee

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2368_2400
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_2368_2400
private theorem valid2368 : RecordDataValid section14Catalog 6 (⟨163,(12),[5,6],[174],970⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨970,[3,5,6,7],974⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2369 : RecordDataValid section14Catalog 6 (⟨163,(13),[1,2,5,6,13,14],[170],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2370 : RecordDataValid section14Catalog 6 (⟨163,(13),[5,6],[174],970⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨970,[3,5,6,7],974⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2371 : RecordDataValid section14Catalog 6 (⟨163,(14),[1,2,5,6,13,14],[170],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2372 : RecordDataValid section14Catalog 6 (⟨163,(14),[5,6],[174],970⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨970,[3,5,6,7],974⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2373 : RecordDataValid section14Catalog 6 (⟨163,(15),[1,2,5,6,13,14],[170],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2374 : RecordDataValid section14Catalog 6 (⟨163,(15),[5,6],[174],970⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨970,[3,5,6,7],974⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2375 : RecordDataValid section14Catalog 6 (⟨166,(0),[1,2,5,6,13,14],[170],644⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨644,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],645⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2376 : RecordDataValid section14Catalog 6 (⟨166,(0),[5,6],[174],644⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨644,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],645⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2377 : RecordDataValid section14Catalog 6 (⟨166,(1),[1,2,5,6,13,14],[170],644⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨644,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],645⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2378 : RecordDataValid section14Catalog 6 (⟨166,(1),[5,6],[174],644⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨644,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],645⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2379 : RecordDataValid section14Catalog 6 (⟨166,(2),[1,2,5,6,13,14],[170],644⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨644,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],645⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2380 : RecordDataValid section14Catalog 6 (⟨166,(2),[5,6],[174],644⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨644,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],645⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2381 : RecordDataValid section14Catalog 6 (⟨166,(3),[1,2,5,6,13,14],[170],644⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨644,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],645⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2382 : RecordDataValid section14Catalog 6 (⟨166,(3),[5,6],[174],644⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨644,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],645⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2383 : RecordDataValid section14Catalog 6 (⟨166,(4),[1,2,5,6,13,14],[170],645⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨645,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],646⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2384 : RecordDataValid section14Catalog 6 (⟨166,(4),[5,6],[174],645⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨645,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],646⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2385 : RecordDataValid section14Catalog 6 (⟨166,(5),[1,2,5,6,13,14],[170],645⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨645,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],646⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2386 : RecordDataValid section14Catalog 6 (⟨166,(5),[5,6],[174],645⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨645,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],646⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2387 : RecordDataValid section14Catalog 6 (⟨166,(6),[1,2,5,6,13,14],[170],645⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨645,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],646⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2388 : RecordDataValid section14Catalog 6 (⟨166,(6),[5,6],[174],645⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨645,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],646⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2389 : RecordDataValid section14Catalog 6 (⟨166,(7),[1,2,5,6,13,14],[170],645⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨645,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],646⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2390 : RecordDataValid section14Catalog 6 (⟨166,(7),[5,6],[174],645⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨645,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],646⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2391 : RecordDataValid section14Catalog 6 (⟨166,(8),[1,2,5,6,13,14],[170],646⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨646,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],647⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2392 : RecordDataValid section14Catalog 6 (⟨166,(8),[5,6],[174],646⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨646,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],647⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2393 : RecordDataValid section14Catalog 6 (⟨166,(9),[1,2,5,6,13,14],[170],647⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨647,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],648⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2394 : RecordDataValid section14Catalog 6 (⟨166,(9),[5,6],[174],647⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨647,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],648⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2395 : RecordDataValid section14Catalog 6 (⟨166,(10),[1,2,5,6,13,14],[170],646⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨646,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],647⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2396 : RecordDataValid section14Catalog 6 (⟨166,(10),[5,6],[174],646⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨646,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],647⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2397 : RecordDataValid section14Catalog 6 (⟨166,(11),[1,2,5,6,13,14],[170],648⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨648,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],649⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2398 : RecordDataValid section14Catalog 6 (⟨166,(11),[5,6],[174],648⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨648,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],649⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2399 : RecordDataValid section14Catalog 6 (⟨166,(12),[1,2,5,6,13,14],[170],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_2368_2400 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2368).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2368).take 32 = [⟨163,(12),[5,6],[174],970⟩,⟨163,(13),[1,2,5,6,13,14],[170],411⟩,⟨163,(13),[5,6],[174],970⟩,⟨163,(14),[1,2,5,6,13,14],[170],411⟩,⟨163,(14),[5,6],[174],970⟩,⟨163,(15),[1,2,5,6,13,14],[170],411⟩,⟨163,(15),[5,6],[174],970⟩,⟨166,(0),[1,2,5,6,13,14],[170],644⟩,⟨166,(0),[5,6],[174],644⟩,⟨166,(1),[1,2,5,6,13,14],[170],644⟩,⟨166,(1),[5,6],[174],644⟩,⟨166,(2),[1,2,5,6,13,14],[170],644⟩,⟨166,(2),[5,6],[174],644⟩,⟨166,(3),[1,2,5,6,13,14],[170],644⟩,⟨166,(3),[5,6],[174],644⟩,⟨166,(4),[1,2,5,6,13,14],[170],645⟩,⟨166,(4),[5,6],[174],645⟩,⟨166,(5),[1,2,5,6,13,14],[170],645⟩,⟨166,(5),[5,6],[174],645⟩,⟨166,(6),[1,2,5,6,13,14],[170],645⟩,⟨166,(6),[5,6],[174],645⟩,⟨166,(7),[1,2,5,6,13,14],[170],645⟩,⟨166,(7),[5,6],[174],645⟩,⟨166,(8),[1,2,5,6,13,14],[170],646⟩,⟨166,(8),[5,6],[174],646⟩,⟨166,(9),[1,2,5,6,13,14],[170],647⟩,⟨166,(9),[5,6],[174],647⟩,⟨166,(10),[1,2,5,6,13,14],[170],646⟩,⟨166,(10),[5,6],[174],646⟩,⟨166,(11),[1,2,5,6,13,14],[170],648⟩,⟨166,(11),[5,6],[174],648⟩,⟨166,(12),[1,2,5,6,13,14],[170],649⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2368
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2369
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2370
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2371
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2372
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2373
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2374
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2375
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2376
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2377
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2378
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2379
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2380
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2381
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2382
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2383
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2384
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2385
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2386
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2387
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2388
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2389
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2390
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2391
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2392
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2393
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2394
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2395
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2396
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2397
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2398
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2399
end Section14Records_6_2368_2400

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2368_2400


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2400_2432
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_2400_2432
private theorem valid2400 : RecordDataValid section14Catalog 6 (⟨166,(12),[5,6],[174],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2401 : RecordDataValid section14Catalog 6 (⟨166,(13),[1,2,5,6,13,14],[170],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2402 : RecordDataValid section14Catalog 6 (⟨166,(13),[5,6],[174],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2403 : RecordDataValid section14Catalog 6 (⟨166,(14),[1,2,5,6,13,14],[170],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2404 : RecordDataValid section14Catalog 6 (⟨166,(14),[5,6],[174],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2405 : RecordDataValid section14Catalog 6 (⟨166,(15),[1,2,5,6,13,14],[170],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2406 : RecordDataValid section14Catalog 6 (⟨166,(15),[5,6],[174],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2407 : RecordDataValid section14Catalog 6 (⟨167,(0),[1,2,5,6,13,14],[170],418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨418,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],419⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2408 : RecordDataValid section14Catalog 6 (⟨167,(0),[5,6],[174],971⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨971,[3,5,6,7],975⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2409 : RecordDataValid section14Catalog 6 (⟨167,(1),[1,2,5,6,13,14],[170],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2410 : RecordDataValid section14Catalog 6 (⟨167,(1),[5,6],[174],972⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨972,[3,5,6,7],976⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2411 : RecordDataValid section14Catalog 6 (⟨167,(2),[1,2,5,6,13,14],[170],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2412 : RecordDataValid section14Catalog 6 (⟨167,(2),[5,6],[174],973⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨973,[3,5,6,7],977⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2413 : RecordDataValid section14Catalog 6 (⟨167,(3),[1,2,5,6,13,14],[170],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2414 : RecordDataValid section14Catalog 6 (⟨167,(3),[5,6],[174],974⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨974,[3,5,6,7],978⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2415 : RecordDataValid section14Catalog 6 (⟨167,(4),[1,2,5,6,13,14],[170],422⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨422,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],423⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2416 : RecordDataValid section14Catalog 6 (⟨167,(4),[5,6],[174],975⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨975,[3,5,6,7],979⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2417 : RecordDataValid section14Catalog 6 (⟨167,(5),[1,2,5,6,13,14],[170],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2418 : RecordDataValid section14Catalog 6 (⟨167,(5),[5,6],[174],972⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨972,[3,5,6,7],976⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2419 : RecordDataValid section14Catalog 6 (⟨167,(6),[1,2,5,6,13,14],[170],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2420 : RecordDataValid section14Catalog 6 (⟨167,(6),[5,6],[174],973⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨973,[3,5,6,7],977⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2421 : RecordDataValid section14Catalog 6 (⟨167,(7),[1,2,5,6,13,14],[170],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2422 : RecordDataValid section14Catalog 6 (⟨167,(7),[5,6],[174],974⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨974,[3,5,6,7],978⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2423 : RecordDataValid section14Catalog 6 (⟨167,(8),[1,2,5,6,13,14],[170],418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨418,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],419⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2424 : RecordDataValid section14Catalog 6 (⟨167,(8),[5,6],[174],971⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨971,[3,5,6,7],975⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2425 : RecordDataValid section14Catalog 6 (⟨167,(9),[1,2,5,6,13,14],[170],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2426 : RecordDataValid section14Catalog 6 (⟨167,(9),[5,6],[174],972⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨972,[3,5,6,7],976⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2427 : RecordDataValid section14Catalog 6 (⟨167,(10),[1,2,5,6,13,14],[170],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2428 : RecordDataValid section14Catalog 6 (⟨167,(10),[5,6],[174],973⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨973,[3,5,6,7],977⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2429 : RecordDataValid section14Catalog 6 (⟨167,(11),[1,2,5,6,13,14],[170],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2430 : RecordDataValid section14Catalog 6 (⟨167,(11),[5,6],[174],974⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨974,[3,5,6,7],978⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2431 : RecordDataValid section14Catalog 6 (⟨167,(12),[1,2,5,6,13,14],[170],423⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨423,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],424⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_2400_2432 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2400).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2400).take 32 = [⟨166,(12),[5,6],[174],649⟩,⟨166,(13),[1,2,5,6,13,14],[170],649⟩,⟨166,(13),[5,6],[174],649⟩,⟨166,(14),[1,2,5,6,13,14],[170],649⟩,⟨166,(14),[5,6],[174],649⟩,⟨166,(15),[1,2,5,6,13,14],[170],649⟩,⟨166,(15),[5,6],[174],649⟩,⟨167,(0),[1,2,5,6,13,14],[170],418⟩,⟨167,(0),[5,6],[174],971⟩,⟨167,(1),[1,2,5,6,13,14],[170],419⟩,⟨167,(1),[5,6],[174],972⟩,⟨167,(2),[1,2,5,6,13,14],[170],420⟩,⟨167,(2),[5,6],[174],973⟩,⟨167,(3),[1,2,5,6,13,14],[170],421⟩,⟨167,(3),[5,6],[174],974⟩,⟨167,(4),[1,2,5,6,13,14],[170],422⟩,⟨167,(4),[5,6],[174],975⟩,⟨167,(5),[1,2,5,6,13,14],[170],419⟩,⟨167,(5),[5,6],[174],972⟩,⟨167,(6),[1,2,5,6,13,14],[170],420⟩,⟨167,(6),[5,6],[174],973⟩,⟨167,(7),[1,2,5,6,13,14],[170],421⟩,⟨167,(7),[5,6],[174],974⟩,⟨167,(8),[1,2,5,6,13,14],[170],418⟩,⟨167,(8),[5,6],[174],971⟩,⟨167,(9),[1,2,5,6,13,14],[170],419⟩,⟨167,(9),[5,6],[174],972⟩,⟨167,(10),[1,2,5,6,13,14],[170],420⟩,⟨167,(10),[5,6],[174],973⟩,⟨167,(11),[1,2,5,6,13,14],[170],421⟩,⟨167,(11),[5,6],[174],974⟩,⟨167,(12),[1,2,5,6,13,14],[170],423⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2400
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2401
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2402
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2403
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2404
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2405
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2406
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2407
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2408
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2409
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2410
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2411
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2412
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2413
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2414
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2415
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2416
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2417
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2418
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2419
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2420
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2421
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2422
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2423
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2424
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2425
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2426
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2427
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2428
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2429
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2430
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2431
end Section14Records_6_2400_2432

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2400_2432

open Freiman
namespace M7Section14Sep18
universe u

theorem all_of_take_drop {α : Type u} (P : α → Prop) (xs : List α) (n : ℕ)
    (ht : ∀ x ∈ xs.take n, P x) (hd : ∀ x ∈ xs.drop n, P x) :
    ∀ x ∈ xs, P x := by
  intro x hx
  have hm : x ∈ xs.take n ++ xs.drop n := by
    simpa only [List.take_append_drop] using hx
  rcases List.mem_append.mp hm with h | h
  · exact ht x h
  · exact hd x h

theorem all_of_chunks {α : Type u} (P : α → Prop) (xs : List α) (lo size : ℕ)
    (ht : ∀ x ∈ (xs.drop lo).take size, P x)
    (hd : ∀ x ∈ xs.drop (lo+size), P x) : ∀ x ∈ xs.drop lo, P x := by
  apply all_of_take_drop P (xs.drop lo) size ht
  simpa only [List.drop_drop] using hd

theorem all_empty {α : Type u} (P : α → Prop) (xs : List α) (h : xs = []) :
    ∀ x ∈ xs, P x := by
  rw [h]
  exact fun x hx => False.elim (List.not_mem_nil hx)
end M7Section14Sep18

namespace M7Section14Sep18
universe u

theorem all_of_interval_split {α : Type u} (P : α → Prop) (xs : List α)
    (lo cut hi : ℕ) (hc : lo ≤ cut) (hh : cut ≤ hi)
    (left : ∀ x ∈ (xs.drop lo).take (cut-lo), P x)
    (right : ∀ x ∈ (xs.drop cut).take (hi-cut), P x) :
    ∀ x ∈ (xs.drop lo).take (hi-lo), P x := by
  have hsum : hi-lo = (cut-lo)+(hi-cut) := by omega
  have hdrop : lo+(cut-lo) = cut := by omega
  rw [hsum, List.take_add, List.drop_drop, hdrop]
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact left x hx
  · exact right x hx
end M7Section14Sep18

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2368).take 64, section14RecordValid section14Catalog 6 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (6 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 6 r
  exact (all_of_interval_split P xs 2368 2400 2432 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_2368_2400 hnum) (Freiman.workReverse20260919_s0006_records_2400_2432 hnum))

#print axioms solution
