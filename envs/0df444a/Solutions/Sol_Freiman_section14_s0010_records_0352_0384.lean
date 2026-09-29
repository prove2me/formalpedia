-- Prove2me | solution 1 for Freiman.section14_s0010_records_0352_0384
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T16:37:57.519985+00:00
-- url     : https://prove2.me/submissions/47cf42ef-f363-4f6c-b70d-d14a9ac1d6d8

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
namespace Section14Records_10_352_384
private theorem valid352 : RecordDataValid section14Catalog 10 (⟨30,(0),[9,10],[34,35,38],152⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨152,[1,2,3,4,5,6,7,8,9,10,11,12],152⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid353 : RecordDataValid section14Catalog 10 (⟨30,(1),[9,10],[34,35,38],153⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨153,[1,2,3,4,5,6,7,8,9,10,11,12],153⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid354 : RecordDataValid section14Catalog 10 (⟨30,(2),[9,10],[34],92⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨92,[1,2,5,6,9,10,12],92⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid355 : RecordDataValid section14Catalog 10 (⟨30,(2),[9,10],[35],120⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨120,[1,2,5,6,9,10],120⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid356 : RecordDataValid section14Catalog 10 (⟨30,(2),[9,10],[38],200⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨200,[1,2,3,4,5,6,7,8,9,10,11,12],200⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid357 : RecordDataValid section14Catalog 10 (⟨30,(3),[9,10],[34],93⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨93,[1,2,5,6,9,10,12],93⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid358 : RecordDataValid section14Catalog 10 (⟨30,(3),[9,10],[35],181⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨181,[1,2,5,6,9,10],181⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid359 : RecordDataValid section14Catalog 10 (⟨30,(3),[9,10],[38],230⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨230,[1,2,3,4,5,6,7,8,9,10,11,12],230⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid360 : RecordDataValid section14Catalog 10 (⟨30,(4),[9,10],[34],94⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨94,[1,2,5,6,9,10,12],94⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid361 : RecordDataValid section14Catalog 10 (⟨30,(4),[9,10],[35],182⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨182,[1,2,5,6,9,10],182⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid362 : RecordDataValid section14Catalog 10 (⟨30,(4),[9,10],[38],231⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨231,[1,2,3,4,5,6,7,8,9,10,11,12],231⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid363 : RecordDataValid section14Catalog 10 (⟨30,(5),[9,10],[34],93⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨93,[1,2,5,6,9,10,12],93⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid364 : RecordDataValid section14Catalog 10 (⟨30,(5),[9,10],[35],181⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨181,[1,2,5,6,9,10],181⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid365 : RecordDataValid section14Catalog 10 (⟨30,(5),[9,10],[38],230⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨230,[1,2,3,4,5,6,7,8,9,10,11,12],230⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid366 : RecordDataValid section14Catalog 10 (⟨30,(6),[9,10],[34],95⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨95,[1,2,5,6,9,10,12],95⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid367 : RecordDataValid section14Catalog 10 (⟨30,(6),[9,10],[35],183⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨183,[1,2,5,6,9,10],183⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid368 : RecordDataValid section14Catalog 10 (⟨30,(6),[9,10],[38],232⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨232,[1,2,3,4,5,6,7,8,9,10,11,12],232⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid369 : RecordDataValid section14Catalog 10 (⟨30,(7),[9,10],[34],95⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨95,[1,2,5,6,9,10,12],95⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid370 : RecordDataValid section14Catalog 10 (⟨30,(7),[9,10],[35],183⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨183,[1,2,5,6,9,10],183⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid371 : RecordDataValid section14Catalog 10 (⟨30,(7),[9,10],[38],232⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨232,[1,2,3,4,5,6,7,8,9,10,11,12],232⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid372 : RecordDataValid section14Catalog 10 (⟨30,(8),[9,10],[34],96⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨96,[1,2,5,6,9,10,12],96⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid373 : RecordDataValid section14Catalog 10 (⟨30,(8),[9,10],[35],184⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨184,[1,2,5,6,9,10],184⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid374 : RecordDataValid section14Catalog 10 (⟨30,(8),[9,10],[38],233⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨233,[1,2,3,4,5,6,7,8,9,10,11,12],233⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid375 : RecordDataValid section14Catalog 10 (⟨30,(9),[9,10],[34],96⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨96,[1,2,5,6,9,10,12],96⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid376 : RecordDataValid section14Catalog 10 (⟨30,(9),[9,10],[35],184⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨184,[1,2,5,6,9,10],184⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid377 : RecordDataValid section14Catalog 10 (⟨30,(9),[9,10],[38],233⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨233,[1,2,3,4,5,6,7,8,9,10,11,12],233⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid378 : RecordDataValid section14Catalog 10 (⟨33,(0),[9,10],[34,35],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid379 : RecordDataValid section14Catalog 10 (⟨33,(0),[10],[38],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid380 : RecordDataValid section14Catalog 10 (⟨33,(1),[9,10],[38],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid381 : RecordDataValid section14Catalog 10 (⟨33,(1),[10],[34,35],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid382 : RecordDataValid section14Catalog 10 (⟨33,(2),[10],[34,35,38],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid383 : RecordDataValid section14Catalog 10 (⟨33,(3),[10],[34,35,38],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 352).take 32, section14RecordValid section14Catalog 10 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 352).take 32 = [⟨30,(0),[9,10],[34,35,38],152⟩,⟨30,(1),[9,10],[34,35,38],153⟩,⟨30,(2),[9,10],[34],92⟩,⟨30,(2),[9,10],[35],120⟩,⟨30,(2),[9,10],[38],200⟩,⟨30,(3),[9,10],[34],93⟩,⟨30,(3),[9,10],[35],181⟩,⟨30,(3),[9,10],[38],230⟩,⟨30,(4),[9,10],[34],94⟩,⟨30,(4),[9,10],[35],182⟩,⟨30,(4),[9,10],[38],231⟩,⟨30,(5),[9,10],[34],93⟩,⟨30,(5),[9,10],[35],181⟩,⟨30,(5),[9,10],[38],230⟩,⟨30,(6),[9,10],[34],95⟩,⟨30,(6),[9,10],[35],183⟩,⟨30,(6),[9,10],[38],232⟩,⟨30,(7),[9,10],[34],95⟩,⟨30,(7),[9,10],[35],183⟩,⟨30,(7),[9,10],[38],232⟩,⟨30,(8),[9,10],[34],96⟩,⟨30,(8),[9,10],[35],184⟩,⟨30,(8),[9,10],[38],233⟩,⟨30,(9),[9,10],[34],96⟩,⟨30,(9),[9,10],[35],184⟩,⟨30,(9),[9,10],[38],233⟩,⟨33,(0),[9,10],[34,35],2⟩,⟨33,(0),[10],[38],2⟩,⟨33,(1),[9,10],[38],2⟩,⟨33,(1),[10],[34,35],2⟩,⟨33,(2),[10],[34,35,38],3⟩,⟨33,(3),[10],[34,35,38],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 10 _ hnum valid352
  · exact recordValid_of_data section14Catalog 10 _ hnum valid353
  · exact recordValid_of_data section14Catalog 10 _ hnum valid354
  · exact recordValid_of_data section14Catalog 10 _ hnum valid355
  · exact recordValid_of_data section14Catalog 10 _ hnum valid356
  · exact recordValid_of_data section14Catalog 10 _ hnum valid357
  · exact recordValid_of_data section14Catalog 10 _ hnum valid358
  · exact recordValid_of_data section14Catalog 10 _ hnum valid359
  · exact recordValid_of_data section14Catalog 10 _ hnum valid360
  · exact recordValid_of_data section14Catalog 10 _ hnum valid361
  · exact recordValid_of_data section14Catalog 10 _ hnum valid362
  · exact recordValid_of_data section14Catalog 10 _ hnum valid363
  · exact recordValid_of_data section14Catalog 10 _ hnum valid364
  · exact recordValid_of_data section14Catalog 10 _ hnum valid365
  · exact recordValid_of_data section14Catalog 10 _ hnum valid366
  · exact recordValid_of_data section14Catalog 10 _ hnum valid367
  · exact recordValid_of_data section14Catalog 10 _ hnum valid368
  · exact recordValid_of_data section14Catalog 10 _ hnum valid369
  · exact recordValid_of_data section14Catalog 10 _ hnum valid370
  · exact recordValid_of_data section14Catalog 10 _ hnum valid371
  · exact recordValid_of_data section14Catalog 10 _ hnum valid372
  · exact recordValid_of_data section14Catalog 10 _ hnum valid373
  · exact recordValid_of_data section14Catalog 10 _ hnum valid374
  · exact recordValid_of_data section14Catalog 10 _ hnum valid375
  · exact recordValid_of_data section14Catalog 10 _ hnum valid376
  · exact recordValid_of_data section14Catalog 10 _ hnum valid377
  · exact recordValid_of_data section14Catalog 10 _ hnum valid378
  · exact recordValid_of_data section14Catalog 10 _ hnum valid379
  · exact recordValid_of_data section14Catalog 10 _ hnum valid380
  · exact recordValid_of_data section14Catalog 10 _ hnum valid381
  · exact recordValid_of_data section14Catalog 10 _ hnum valid382
  · exact recordValid_of_data section14Catalog 10 _ hnum valid383
end Section14Records_10_352_384

#print axioms solution
