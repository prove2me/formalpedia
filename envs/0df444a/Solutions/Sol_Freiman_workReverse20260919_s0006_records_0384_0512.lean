-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_0384_0512
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:46:59.235559+00:00
-- url     : https://prove2.me/submissions/8c5459b3-b66b-4f70-84da-d9741af45713

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0384_0416
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_384_416
private theorem valid384 : RecordDataValid section14Catalog 6 (⟨23,(22),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid385 : RecordDataValid section14Catalog 6 (⟨23,(23),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid386 : RecordDataValid section14Catalog 6 (⟨23,(23),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid387 : RecordDataValid section14Catalog 6 (⟨23,(24),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid388 : RecordDataValid section14Catalog 6 (⟨23,(24),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid389 : RecordDataValid section14Catalog 6 (⟨25,(0),[1,2,5,6],[130],80⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨80,[1,2,5,6,9,10,12,13,14],80⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid390 : RecordDataValid section14Catalog 6 (⟨25,(0),[1,2,5,6,13,14],[146],145⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨145,[1,2,3,5,6,7,13,14,15],145⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid391 : RecordDataValid section14Catalog 6 (⟨25,(0),[1,2,5,6,13,14],[150],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid392 : RecordDataValid section14Catalog 6 (⟨25,(0),[5,6],[131],167⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨167,[1,2,5,6,9,10,13,14],167⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid393 : RecordDataValid section14Catalog 6 (⟨25,(1),[1,2,5,6],[130],81⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨81,[1,2,5,6,9,10,12,13,14],81⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid394 : RecordDataValid section14Catalog 6 (⟨25,(1),[1,2,5,6,13,14],[146],146⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨146,[1,2,3,5,6,7,13,14,15],146⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid395 : RecordDataValid section14Catalog 6 (⟨25,(1),[5,6],[131],168⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨168,[1,2,5,6,9,10,13,14],168⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid396 : RecordDataValid section14Catalog 6 (⟨25,(1),[5,6],[150],216⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨216,[1,2,3,5,6,7,8,9,10,11,12,13,14,15],216⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid397 : RecordDataValid section14Catalog 6 (⟨25,(2),[1,2,5,6],[130],80⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨80,[1,2,5,6,9,10,12,13,14],80⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid398 : RecordDataValid section14Catalog 6 (⟨25,(2),[1,2,5,6,13,14],[146],145⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨145,[1,2,3,5,6,7,13,14,15],145⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid399 : RecordDataValid section14Catalog 6 (⟨25,(2),[5,6],[131],167⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨167,[1,2,5,6,9,10,13,14],167⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid400 : RecordDataValid section14Catalog 6 (⟨25,(2),[5,6],[150],217⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨217,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],217⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid401 : RecordDataValid section14Catalog 6 (⟨25,(3),[1,2,5,6],[130],82⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨82,[1,2,5,6,9,10,12,13,14],82⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid402 : RecordDataValid section14Catalog 6 (⟨25,(3),[1,2,5,6,13,14],[146],147⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨147,[1,2,3,5,6,7,13,14,15],147⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid403 : RecordDataValid section14Catalog 6 (⟨25,(3),[5,6],[131],169⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨169,[1,2,5,6,9,10,13,14],169⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid404 : RecordDataValid section14Catalog 6 (⟨25,(3),[5,6],[150],218⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨218,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],218⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid405 : RecordDataValid section14Catalog 6 (⟨25,(4),[1,2,5,6],[130],83⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨83,[1,2,5,6,9,10,12,13,14],83⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid406 : RecordDataValid section14Catalog 6 (⟨25,(4),[1,2,5,6,13,14],[146],148⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨148,[1,2,3,5,6,7,13,14,15],148⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid407 : RecordDataValid section14Catalog 6 (⟨25,(4),[5,6],[131],170⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨170,[1,2,5,6,9,10,13,14],170⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid408 : RecordDataValid section14Catalog 6 (⟨25,(4),[5,6],[150],219⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨219,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],219⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid409 : RecordDataValid section14Catalog 6 (⟨25,(5),[1,2,5,6],[130],80⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨80,[1,2,5,6,9,10,12,13,14],80⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid410 : RecordDataValid section14Catalog 6 (⟨25,(5),[1,2,5,6,13,14],[146],145⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨145,[1,2,3,5,6,7,13,14,15],145⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid411 : RecordDataValid section14Catalog 6 (⟨25,(5),[1,2,5,6,13,14],[150],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid412 : RecordDataValid section14Catalog 6 (⟨25,(5),[5,6],[131],167⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨167,[1,2,5,6,9,10,13,14],167⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid413 : RecordDataValid section14Catalog 6 (⟨25,(6),[1,2,5,6],[130],81⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨81,[1,2,5,6,9,10,12,13,14],81⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid414 : RecordDataValid section14Catalog 6 (⟨25,(6),[1,2,5,6,13,14],[146],146⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨146,[1,2,3,5,6,7,13,14,15],146⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid415 : RecordDataValid section14Catalog 6 (⟨25,(6),[5,6],[131],168⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨168,[1,2,5,6,9,10,13,14],168⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_0384_0416 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 384).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 384).take 32 = [⟨23,(22),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(23),[1,2,5,6],[130],2⟩,⟨23,(23),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(24),[1,2,5,6],[130],2⟩,⟨23,(24),[1,2,5,6,13,14],[131,146,150],2⟩,⟨25,(0),[1,2,5,6],[130],80⟩,⟨25,(0),[1,2,5,6,13,14],[146],145⟩,⟨25,(0),[1,2,5,6,13,14],[150],189⟩,⟨25,(0),[5,6],[131],167⟩,⟨25,(1),[1,2,5,6],[130],81⟩,⟨25,(1),[1,2,5,6,13,14],[146],146⟩,⟨25,(1),[5,6],[131],168⟩,⟨25,(1),[5,6],[150],216⟩,⟨25,(2),[1,2,5,6],[130],80⟩,⟨25,(2),[1,2,5,6,13,14],[146],145⟩,⟨25,(2),[5,6],[131],167⟩,⟨25,(2),[5,6],[150],217⟩,⟨25,(3),[1,2,5,6],[130],82⟩,⟨25,(3),[1,2,5,6,13,14],[146],147⟩,⟨25,(3),[5,6],[131],169⟩,⟨25,(3),[5,6],[150],218⟩,⟨25,(4),[1,2,5,6],[130],83⟩,⟨25,(4),[1,2,5,6,13,14],[146],148⟩,⟨25,(4),[5,6],[131],170⟩,⟨25,(4),[5,6],[150],219⟩,⟨25,(5),[1,2,5,6],[130],80⟩,⟨25,(5),[1,2,5,6,13,14],[146],145⟩,⟨25,(5),[1,2,5,6,13,14],[150],189⟩,⟨25,(5),[5,6],[131],167⟩,⟨25,(6),[1,2,5,6],[130],81⟩,⟨25,(6),[1,2,5,6,13,14],[146],146⟩,⟨25,(6),[5,6],[131],168⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid384
  · exact recordValid_of_data section14Catalog 6 _ hnum valid385
  · exact recordValid_of_data section14Catalog 6 _ hnum valid386
  · exact recordValid_of_data section14Catalog 6 _ hnum valid387
  · exact recordValid_of_data section14Catalog 6 _ hnum valid388
  · exact recordValid_of_data section14Catalog 6 _ hnum valid389
  · exact recordValid_of_data section14Catalog 6 _ hnum valid390
  · exact recordValid_of_data section14Catalog 6 _ hnum valid391
  · exact recordValid_of_data section14Catalog 6 _ hnum valid392
  · exact recordValid_of_data section14Catalog 6 _ hnum valid393
  · exact recordValid_of_data section14Catalog 6 _ hnum valid394
  · exact recordValid_of_data section14Catalog 6 _ hnum valid395
  · exact recordValid_of_data section14Catalog 6 _ hnum valid396
  · exact recordValid_of_data section14Catalog 6 _ hnum valid397
  · exact recordValid_of_data section14Catalog 6 _ hnum valid398
  · exact recordValid_of_data section14Catalog 6 _ hnum valid399
  · exact recordValid_of_data section14Catalog 6 _ hnum valid400
  · exact recordValid_of_data section14Catalog 6 _ hnum valid401
  · exact recordValid_of_data section14Catalog 6 _ hnum valid402
  · exact recordValid_of_data section14Catalog 6 _ hnum valid403
  · exact recordValid_of_data section14Catalog 6 _ hnum valid404
  · exact recordValid_of_data section14Catalog 6 _ hnum valid405
  · exact recordValid_of_data section14Catalog 6 _ hnum valid406
  · exact recordValid_of_data section14Catalog 6 _ hnum valid407
  · exact recordValid_of_data section14Catalog 6 _ hnum valid408
  · exact recordValid_of_data section14Catalog 6 _ hnum valid409
  · exact recordValid_of_data section14Catalog 6 _ hnum valid410
  · exact recordValid_of_data section14Catalog 6 _ hnum valid411
  · exact recordValid_of_data section14Catalog 6 _ hnum valid412
  · exact recordValid_of_data section14Catalog 6 _ hnum valid413
  · exact recordValid_of_data section14Catalog 6 _ hnum valid414
  · exact recordValid_of_data section14Catalog 6 _ hnum valid415
end Section14Records_6_384_416

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0384_0416


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0416_0448
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_416_448
private theorem valid416 : RecordDataValid section14Catalog 6 (⟨25,(6),[5,6],[150],216⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨216,[1,2,3,5,6,7,8,9,10,11,12,13,14,15],216⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid417 : RecordDataValid section14Catalog 6 (⟨25,(7),[1,2,5,6],[130],80⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨80,[1,2,5,6,9,10,12,13,14],80⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid418 : RecordDataValid section14Catalog 6 (⟨25,(7),[1,2,5,6,13,14],[146],145⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨145,[1,2,3,5,6,7,13,14,15],145⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid419 : RecordDataValid section14Catalog 6 (⟨25,(7),[5,6],[131],167⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨167,[1,2,5,6,9,10,13,14],167⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid420 : RecordDataValid section14Catalog 6 (⟨25,(7),[5,6],[150],217⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨217,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],217⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid421 : RecordDataValid section14Catalog 6 (⟨25,(8),[1,2,5,6],[130],82⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨82,[1,2,5,6,9,10,12,13,14],82⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid422 : RecordDataValid section14Catalog 6 (⟨25,(8),[1,2,5,6,13,14],[146],147⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨147,[1,2,3,5,6,7,13,14,15],147⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid423 : RecordDataValid section14Catalog 6 (⟨25,(8),[5,6],[131],169⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨169,[1,2,5,6,9,10,13,14],169⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid424 : RecordDataValid section14Catalog 6 (⟨25,(8),[5,6],[150],218⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨218,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],218⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid425 : RecordDataValid section14Catalog 6 (⟨25,(9),[1,2,5,6],[130],83⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨83,[1,2,5,6,9,10,12,13,14],83⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid426 : RecordDataValid section14Catalog 6 (⟨25,(9),[1,2,5,6,13,14],[146],148⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨148,[1,2,3,5,6,7,13,14,15],148⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid427 : RecordDataValid section14Catalog 6 (⟨25,(9),[5,6],[131],170⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨170,[1,2,5,6,9,10,13,14],170⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid428 : RecordDataValid section14Catalog 6 (⟨25,(9),[5,6],[150],219⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨219,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],219⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid429 : RecordDataValid section14Catalog 6 (⟨25,(10),[1,2,5,6],[130],84⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid430 : RecordDataValid section14Catalog 6 (⟨25,(10),[1,2,5,6,13,14],[146],149⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨149,[1,2,3,5,6,7,13,14,15],149⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid431 : RecordDataValid section14Catalog 6 (⟨25,(10),[1,2,5,6,13,14],[150],194⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨194,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],194⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid432 : RecordDataValid section14Catalog 6 (⟨25,(10),[5,6],[131],171⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨171,[1,2,5,6,9,10,13,14],171⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid433 : RecordDataValid section14Catalog 6 (⟨25,(11),[1,2,5,6],[130],84⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid434 : RecordDataValid section14Catalog 6 (⟨25,(11),[1,2,5,6,13,14],[146],149⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨149,[1,2,3,5,6,7,13,14,15],149⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid435 : RecordDataValid section14Catalog 6 (⟨25,(11),[5,6],[131],171⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨171,[1,2,5,6,9,10,13,14],171⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid436 : RecordDataValid section14Catalog 6 (⟨25,(11),[5,6],[150],220⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨220,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],220⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid437 : RecordDataValid section14Catalog 6 (⟨25,(12),[1,2,5,6],[130],84⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid438 : RecordDataValid section14Catalog 6 (⟨25,(12),[1,2,5,6,13,14],[146],149⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨149,[1,2,3,5,6,7,13,14,15],149⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid439 : RecordDataValid section14Catalog 6 (⟨25,(12),[5,6],[131],171⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨171,[1,2,5,6,9,10,13,14],171⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid440 : RecordDataValid section14Catalog 6 (⟨25,(12),[5,6],[150],220⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨220,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],220⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid441 : RecordDataValid section14Catalog 6 (⟨25,(13),[1,2,5,6],[130],84⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid442 : RecordDataValid section14Catalog 6 (⟨25,(13),[1,2,5,6,13,14],[146],149⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨149,[1,2,3,5,6,7,13,14,15],149⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid443 : RecordDataValid section14Catalog 6 (⟨25,(13),[5,6],[131],171⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨171,[1,2,5,6,9,10,13,14],171⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid444 : RecordDataValid section14Catalog 6 (⟨25,(13),[5,6],[150],220⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨220,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],220⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid445 : RecordDataValid section14Catalog 6 (⟨25,(14),[1,2,5,6],[130],83⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨83,[1,2,5,6,9,10,12,13,14],83⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid446 : RecordDataValid section14Catalog 6 (⟨25,(14),[1,2,5,6,13,14],[146],148⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨148,[1,2,3,5,6,7,13,14,15],148⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid447 : RecordDataValid section14Catalog 6 (⟨25,(14),[5,6],[131],170⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨170,[1,2,5,6,9,10,13,14],170⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_0416_0448 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 416).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 416).take 32 = [⟨25,(6),[5,6],[150],216⟩,⟨25,(7),[1,2,5,6],[130],80⟩,⟨25,(7),[1,2,5,6,13,14],[146],145⟩,⟨25,(7),[5,6],[131],167⟩,⟨25,(7),[5,6],[150],217⟩,⟨25,(8),[1,2,5,6],[130],82⟩,⟨25,(8),[1,2,5,6,13,14],[146],147⟩,⟨25,(8),[5,6],[131],169⟩,⟨25,(8),[5,6],[150],218⟩,⟨25,(9),[1,2,5,6],[130],83⟩,⟨25,(9),[1,2,5,6,13,14],[146],148⟩,⟨25,(9),[5,6],[131],170⟩,⟨25,(9),[5,6],[150],219⟩,⟨25,(10),[1,2,5,6],[130],84⟩,⟨25,(10),[1,2,5,6,13,14],[146],149⟩,⟨25,(10),[1,2,5,6,13,14],[150],194⟩,⟨25,(10),[5,6],[131],171⟩,⟨25,(11),[1,2,5,6],[130],84⟩,⟨25,(11),[1,2,5,6,13,14],[146],149⟩,⟨25,(11),[5,6],[131],171⟩,⟨25,(11),[5,6],[150],220⟩,⟨25,(12),[1,2,5,6],[130],84⟩,⟨25,(12),[1,2,5,6,13,14],[146],149⟩,⟨25,(12),[5,6],[131],171⟩,⟨25,(12),[5,6],[150],220⟩,⟨25,(13),[1,2,5,6],[130],84⟩,⟨25,(13),[1,2,5,6,13,14],[146],149⟩,⟨25,(13),[5,6],[131],171⟩,⟨25,(13),[5,6],[150],220⟩,⟨25,(14),[1,2,5,6],[130],83⟩,⟨25,(14),[1,2,5,6,13,14],[146],148⟩,⟨25,(14),[5,6],[131],170⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid416
  · exact recordValid_of_data section14Catalog 6 _ hnum valid417
  · exact recordValid_of_data section14Catalog 6 _ hnum valid418
  · exact recordValid_of_data section14Catalog 6 _ hnum valid419
  · exact recordValid_of_data section14Catalog 6 _ hnum valid420
  · exact recordValid_of_data section14Catalog 6 _ hnum valid421
  · exact recordValid_of_data section14Catalog 6 _ hnum valid422
  · exact recordValid_of_data section14Catalog 6 _ hnum valid423
  · exact recordValid_of_data section14Catalog 6 _ hnum valid424
  · exact recordValid_of_data section14Catalog 6 _ hnum valid425
  · exact recordValid_of_data section14Catalog 6 _ hnum valid426
  · exact recordValid_of_data section14Catalog 6 _ hnum valid427
  · exact recordValid_of_data section14Catalog 6 _ hnum valid428
  · exact recordValid_of_data section14Catalog 6 _ hnum valid429
  · exact recordValid_of_data section14Catalog 6 _ hnum valid430
  · exact recordValid_of_data section14Catalog 6 _ hnum valid431
  · exact recordValid_of_data section14Catalog 6 _ hnum valid432
  · exact recordValid_of_data section14Catalog 6 _ hnum valid433
  · exact recordValid_of_data section14Catalog 6 _ hnum valid434
  · exact recordValid_of_data section14Catalog 6 _ hnum valid435
  · exact recordValid_of_data section14Catalog 6 _ hnum valid436
  · exact recordValid_of_data section14Catalog 6 _ hnum valid437
  · exact recordValid_of_data section14Catalog 6 _ hnum valid438
  · exact recordValid_of_data section14Catalog 6 _ hnum valid439
  · exact recordValid_of_data section14Catalog 6 _ hnum valid440
  · exact recordValid_of_data section14Catalog 6 _ hnum valid441
  · exact recordValid_of_data section14Catalog 6 _ hnum valid442
  · exact recordValid_of_data section14Catalog 6 _ hnum valid443
  · exact recordValid_of_data section14Catalog 6 _ hnum valid444
  · exact recordValid_of_data section14Catalog 6 _ hnum valid445
  · exact recordValid_of_data section14Catalog 6 _ hnum valid446
  · exact recordValid_of_data section14Catalog 6 _ hnum valid447
end Section14Records_6_416_448

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0416_0448


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0448_0480
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_448_480
private theorem valid448 : RecordDataValid section14Catalog 6 (⟨25,(14),[5,6],[150],219⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨219,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],219⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid449 : RecordDataValid section14Catalog 6 (⟨25,(15),[1,2,5,6],[130],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid450 : RecordDataValid section14Catalog 6 (⟨25,(15),[1,2,5,6,13,14],[146],150⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨150,[1,2,3,5,6,7,13,14,15],150⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid451 : RecordDataValid section14Catalog 6 (⟨25,(15),[1,2,5,6,13,14],[150],196⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨196,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],196⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid452 : RecordDataValid section14Catalog 6 (⟨25,(15),[5,6],[131],172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨172,[1,2,5,6,9,10,13,14],172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid453 : RecordDataValid section14Catalog 6 (⟨25,(16),[1,2,5,6],[130],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid454 : RecordDataValid section14Catalog 6 (⟨25,(16),[1,2,5,6,13,14],[146],150⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨150,[1,2,3,5,6,7,13,14,15],150⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid455 : RecordDataValid section14Catalog 6 (⟨25,(16),[5,6],[131],172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨172,[1,2,5,6,9,10,13,14],172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid456 : RecordDataValid section14Catalog 6 (⟨25,(16),[5,6],[150],221⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨221,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],221⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid457 : RecordDataValid section14Catalog 6 (⟨25,(17),[1,2,5,6],[130],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid458 : RecordDataValid section14Catalog 6 (⟨25,(17),[1,2,5,6,13,14],[146],150⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨150,[1,2,3,5,6,7,13,14,15],150⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid459 : RecordDataValid section14Catalog 6 (⟨25,(17),[5,6],[131],172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨172,[1,2,5,6,9,10,13,14],172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid460 : RecordDataValid section14Catalog 6 (⟨25,(17),[5,6],[150],221⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨221,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],221⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid461 : RecordDataValid section14Catalog 6 (⟨25,(18),[1,2,5,6],[130],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid462 : RecordDataValid section14Catalog 6 (⟨25,(18),[1,2,5,6,13,14],[146],150⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨150,[1,2,3,5,6,7,13,14,15],150⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid463 : RecordDataValid section14Catalog 6 (⟨25,(18),[5,6],[131],172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨172,[1,2,5,6,9,10,13,14],172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid464 : RecordDataValid section14Catalog 6 (⟨25,(18),[5,6],[150],221⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨221,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],221⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid465 : RecordDataValid section14Catalog 6 (⟨25,(19),[1,2,5,6],[130],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid466 : RecordDataValid section14Catalog 6 (⟨25,(19),[1,2,5,6,13,14],[146],150⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨150,[1,2,3,5,6,7,13,14,15],150⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid467 : RecordDataValid section14Catalog 6 (⟨25,(19),[5,6],[131],172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨172,[1,2,5,6,9,10,13,14],172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid468 : RecordDataValid section14Catalog 6 (⟨25,(19),[5,6],[150],221⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨221,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],221⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid469 : RecordDataValid section14Catalog 6 (⟨25,(20),[1,2,5,6],[130],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid470 : RecordDataValid section14Catalog 6 (⟨25,(20),[1,2,5,6,13,14],[146],151⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨151,[1,2,3,5,6,7,13,14,15],151⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid471 : RecordDataValid section14Catalog 6 (⟨25,(20),[1,2,5,6,13,14],[150],198⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨198,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],198⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid472 : RecordDataValid section14Catalog 6 (⟨25,(20),[5,6],[131],173⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨173,[1,2,5,6,9,10,13,14],173⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid473 : RecordDataValid section14Catalog 6 (⟨25,(21),[1,2,5,6],[130],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid474 : RecordDataValid section14Catalog 6 (⟨25,(21),[1,2,5,6,13,14],[146],151⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨151,[1,2,3,5,6,7,13,14,15],151⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid475 : RecordDataValid section14Catalog 6 (⟨25,(21),[5,6],[131],173⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨173,[1,2,5,6,9,10,13,14],173⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid476 : RecordDataValid section14Catalog 6 (⟨25,(21),[5,6],[150],222⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨222,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],222⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid477 : RecordDataValid section14Catalog 6 (⟨25,(22),[1,2,5,6],[130],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid478 : RecordDataValid section14Catalog 6 (⟨25,(22),[1,2,5,6,13,14],[146],151⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨151,[1,2,3,5,6,7,13,14,15],151⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid479 : RecordDataValid section14Catalog 6 (⟨25,(22),[5,6],[131],173⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨173,[1,2,5,6,9,10,13,14],173⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_0448_0480 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 448).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 448).take 32 = [⟨25,(14),[5,6],[150],219⟩,⟨25,(15),[1,2,5,6],[130],35⟩,⟨25,(15),[1,2,5,6,13,14],[146],150⟩,⟨25,(15),[1,2,5,6,13,14],[150],196⟩,⟨25,(15),[5,6],[131],172⟩,⟨25,(16),[1,2,5,6],[130],35⟩,⟨25,(16),[1,2,5,6,13,14],[146],150⟩,⟨25,(16),[5,6],[131],172⟩,⟨25,(16),[5,6],[150],221⟩,⟨25,(17),[1,2,5,6],[130],35⟩,⟨25,(17),[1,2,5,6,13,14],[146],150⟩,⟨25,(17),[5,6],[131],172⟩,⟨25,(17),[5,6],[150],221⟩,⟨25,(18),[1,2,5,6],[130],35⟩,⟨25,(18),[1,2,5,6,13,14],[146],150⟩,⟨25,(18),[5,6],[131],172⟩,⟨25,(18),[5,6],[150],221⟩,⟨25,(19),[1,2,5,6],[130],35⟩,⟨25,(19),[1,2,5,6,13,14],[146],150⟩,⟨25,(19),[5,6],[131],172⟩,⟨25,(19),[5,6],[150],221⟩,⟨25,(20),[1,2,5,6],[130],38⟩,⟨25,(20),[1,2,5,6,13,14],[146],151⟩,⟨25,(20),[1,2,5,6,13,14],[150],198⟩,⟨25,(20),[5,6],[131],173⟩,⟨25,(21),[1,2,5,6],[130],38⟩,⟨25,(21),[1,2,5,6,13,14],[146],151⟩,⟨25,(21),[5,6],[131],173⟩,⟨25,(21),[5,6],[150],222⟩,⟨25,(22),[1,2,5,6],[130],38⟩,⟨25,(22),[1,2,5,6,13,14],[146],151⟩,⟨25,(22),[5,6],[131],173⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid448
  · exact recordValid_of_data section14Catalog 6 _ hnum valid449
  · exact recordValid_of_data section14Catalog 6 _ hnum valid450
  · exact recordValid_of_data section14Catalog 6 _ hnum valid451
  · exact recordValid_of_data section14Catalog 6 _ hnum valid452
  · exact recordValid_of_data section14Catalog 6 _ hnum valid453
  · exact recordValid_of_data section14Catalog 6 _ hnum valid454
  · exact recordValid_of_data section14Catalog 6 _ hnum valid455
  · exact recordValid_of_data section14Catalog 6 _ hnum valid456
  · exact recordValid_of_data section14Catalog 6 _ hnum valid457
  · exact recordValid_of_data section14Catalog 6 _ hnum valid458
  · exact recordValid_of_data section14Catalog 6 _ hnum valid459
  · exact recordValid_of_data section14Catalog 6 _ hnum valid460
  · exact recordValid_of_data section14Catalog 6 _ hnum valid461
  · exact recordValid_of_data section14Catalog 6 _ hnum valid462
  · exact recordValid_of_data section14Catalog 6 _ hnum valid463
  · exact recordValid_of_data section14Catalog 6 _ hnum valid464
  · exact recordValid_of_data section14Catalog 6 _ hnum valid465
  · exact recordValid_of_data section14Catalog 6 _ hnum valid466
  · exact recordValid_of_data section14Catalog 6 _ hnum valid467
  · exact recordValid_of_data section14Catalog 6 _ hnum valid468
  · exact recordValid_of_data section14Catalog 6 _ hnum valid469
  · exact recordValid_of_data section14Catalog 6 _ hnum valid470
  · exact recordValid_of_data section14Catalog 6 _ hnum valid471
  · exact recordValid_of_data section14Catalog 6 _ hnum valid472
  · exact recordValid_of_data section14Catalog 6 _ hnum valid473
  · exact recordValid_of_data section14Catalog 6 _ hnum valid474
  · exact recordValid_of_data section14Catalog 6 _ hnum valid475
  · exact recordValid_of_data section14Catalog 6 _ hnum valid476
  · exact recordValid_of_data section14Catalog 6 _ hnum valid477
  · exact recordValid_of_data section14Catalog 6 _ hnum valid478
  · exact recordValid_of_data section14Catalog 6 _ hnum valid479
end Section14Records_6_448_480

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0448_0480


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0480_0512
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_480_512
private theorem valid480 : RecordDataValid section14Catalog 6 (⟨25,(22),[5,6],[150],222⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨222,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],222⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid481 : RecordDataValid section14Catalog 6 (⟨25,(23),[1,2,5,6],[130],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid482 : RecordDataValid section14Catalog 6 (⟨25,(23),[1,2,5,6,13,14],[146],151⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨151,[1,2,3,5,6,7,13,14,15],151⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid483 : RecordDataValid section14Catalog 6 (⟨25,(23),[5,6],[131],173⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨173,[1,2,5,6,9,10,13,14],173⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid484 : RecordDataValid section14Catalog 6 (⟨25,(23),[5,6],[150],222⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨222,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],222⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid485 : RecordDataValid section14Catalog 6 (⟨25,(24),[1,2,5,6],[130],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid486 : RecordDataValid section14Catalog 6 (⟨25,(24),[1,2,5,6,13,14],[146],151⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨151,[1,2,3,5,6,7,13,14,15],151⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid487 : RecordDataValid section14Catalog 6 (⟨25,(24),[5,6],[131],173⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨173,[1,2,5,6,9,10,13,14],173⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid488 : RecordDataValid section14Catalog 6 (⟨25,(24),[5,6],[150],222⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨222,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],222⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid489 : RecordDataValid section14Catalog 6 (⟨28,(0),[1,2,5,6],[131],113⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨113,[1,2,3,5,6,7,9,10,11],113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid490 : RecordDataValid section14Catalog 6 (⟨28,(0),[1,2,5,6],[150],132⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨132,[1,2,3,5,6,7],132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid491 : RecordDataValid section14Catalog 6 (⟨28,(0),[2,6],[130],113⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨113,[1,2,3,5,6,7,9,10,11],113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid492 : RecordDataValid section14Catalog 6 (⟨28,(0),[6],[146],1520⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1520,[6],1525⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid493 : RecordDataValid section14Catalog 6 (⟨28,(1),[1,2,5,6],[131],113⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨113,[1,2,3,5,6,7,9,10,11],113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid494 : RecordDataValid section14Catalog 6 (⟨28,(1),[1,2,5,6],[150],132⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨132,[1,2,3,5,6,7],132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid495 : RecordDataValid section14Catalog 6 (⟨28,(1),[2,6],[130],113⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨113,[1,2,3,5,6,7,9,10,11],113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid496 : RecordDataValid section14Catalog 6 (⟨28,(1),[6],[146],1520⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1520,[6],1525⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid497 : RecordDataValid section14Catalog 6 (⟨28,(2),[1,2,5,6],[131],113⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨113,[1,2,3,5,6,7,9,10,11],113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid498 : RecordDataValid section14Catalog 6 (⟨28,(2),[1,2,5,6],[150],132⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨132,[1,2,3,5,6,7],132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid499 : RecordDataValid section14Catalog 6 (⟨28,(2),[2,6],[130],113⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨113,[1,2,3,5,6,7,9,10,11],113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid500 : RecordDataValid section14Catalog 6 (⟨28,(2),[6],[146],1520⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1520,[6],1525⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid501 : RecordDataValid section14Catalog 6 (⟨28,(3),[1,2,5,6],[131],113⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨113,[1,2,3,5,6,7,9,10,11],113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid502 : RecordDataValid section14Catalog 6 (⟨28,(3),[1,2,5,6],[150],132⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨132,[1,2,3,5,6,7],132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid503 : RecordDataValid section14Catalog 6 (⟨28,(3),[2,6],[130],113⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨113,[1,2,3,5,6,7,9,10,11],113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid504 : RecordDataValid section14Catalog 6 (⟨28,(3),[6],[146],1520⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1520,[6],1525⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid505 : RecordDataValid section14Catalog 6 (⟨28,(4),[1,2,5,6],[131],113⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨113,[1,2,3,5,6,7,9,10,11],113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid506 : RecordDataValid section14Catalog 6 (⟨28,(4),[1,2,5,6],[150],132⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨132,[1,2,3,5,6,7],132⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid507 : RecordDataValid section14Catalog 6 (⟨28,(4),[2,6],[130],113⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨113,[1,2,3,5,6,7,9,10,11],113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid508 : RecordDataValid section14Catalog 6 (⟨28,(4),[6],[146],1520⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1520,[6],1525⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid509 : RecordDataValid section14Catalog 6 (⟨28,(5),[1,2,5,6],[131],114⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨114,[1,2,3,5,6,7,9,10,11],114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid510 : RecordDataValid section14Catalog 6 (⟨28,(5),[1,2,5,6],[150],133⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨133,[1,2,3,5,6,7],133⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid511 : RecordDataValid section14Catalog 6 (⟨28,(5),[2,6],[130],114⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨114,[1,2,3,5,6,7,9,10,11],114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_0480_0512 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 480).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 480).take 32 = [⟨25,(22),[5,6],[150],222⟩,⟨25,(23),[1,2,5,6],[130],38⟩,⟨25,(23),[1,2,5,6,13,14],[146],151⟩,⟨25,(23),[5,6],[131],173⟩,⟨25,(23),[5,6],[150],222⟩,⟨25,(24),[1,2,5,6],[130],38⟩,⟨25,(24),[1,2,5,6,13,14],[146],151⟩,⟨25,(24),[5,6],[131],173⟩,⟨25,(24),[5,6],[150],222⟩,⟨28,(0),[1,2,5,6],[131],113⟩,⟨28,(0),[1,2,5,6],[150],132⟩,⟨28,(0),[2,6],[130],113⟩,⟨28,(0),[6],[146],1520⟩,⟨28,(1),[1,2,5,6],[131],113⟩,⟨28,(1),[1,2,5,6],[150],132⟩,⟨28,(1),[2,6],[130],113⟩,⟨28,(1),[6],[146],1520⟩,⟨28,(2),[1,2,5,6],[131],113⟩,⟨28,(2),[1,2,5,6],[150],132⟩,⟨28,(2),[2,6],[130],113⟩,⟨28,(2),[6],[146],1520⟩,⟨28,(3),[1,2,5,6],[131],113⟩,⟨28,(3),[1,2,5,6],[150],132⟩,⟨28,(3),[2,6],[130],113⟩,⟨28,(3),[6],[146],1520⟩,⟨28,(4),[1,2,5,6],[131],113⟩,⟨28,(4),[1,2,5,6],[150],132⟩,⟨28,(4),[2,6],[130],113⟩,⟨28,(4),[6],[146],1520⟩,⟨28,(5),[1,2,5,6],[131],114⟩,⟨28,(5),[1,2,5,6],[150],133⟩,⟨28,(5),[2,6],[130],114⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid480
  · exact recordValid_of_data section14Catalog 6 _ hnum valid481
  · exact recordValid_of_data section14Catalog 6 _ hnum valid482
  · exact recordValid_of_data section14Catalog 6 _ hnum valid483
  · exact recordValid_of_data section14Catalog 6 _ hnum valid484
  · exact recordValid_of_data section14Catalog 6 _ hnum valid485
  · exact recordValid_of_data section14Catalog 6 _ hnum valid486
  · exact recordValid_of_data section14Catalog 6 _ hnum valid487
  · exact recordValid_of_data section14Catalog 6 _ hnum valid488
  · exact recordValid_of_data section14Catalog 6 _ hnum valid489
  · exact recordValid_of_data section14Catalog 6 _ hnum valid490
  · exact recordValid_of_data section14Catalog 6 _ hnum valid491
  · exact recordValid_of_data section14Catalog 6 _ hnum valid492
  · exact recordValid_of_data section14Catalog 6 _ hnum valid493
  · exact recordValid_of_data section14Catalog 6 _ hnum valid494
  · exact recordValid_of_data section14Catalog 6 _ hnum valid495
  · exact recordValid_of_data section14Catalog 6 _ hnum valid496
  · exact recordValid_of_data section14Catalog 6 _ hnum valid497
  · exact recordValid_of_data section14Catalog 6 _ hnum valid498
  · exact recordValid_of_data section14Catalog 6 _ hnum valid499
  · exact recordValid_of_data section14Catalog 6 _ hnum valid500
  · exact recordValid_of_data section14Catalog 6 _ hnum valid501
  · exact recordValid_of_data section14Catalog 6 _ hnum valid502
  · exact recordValid_of_data section14Catalog 6 _ hnum valid503
  · exact recordValid_of_data section14Catalog 6 _ hnum valid504
  · exact recordValid_of_data section14Catalog 6 _ hnum valid505
  · exact recordValid_of_data section14Catalog 6 _ hnum valid506
  · exact recordValid_of_data section14Catalog 6 _ hnum valid507
  · exact recordValid_of_data section14Catalog 6 _ hnum valid508
  · exact recordValid_of_data section14Catalog 6 _ hnum valid509
  · exact recordValid_of_data section14Catalog 6 _ hnum valid510
  · exact recordValid_of_data section14Catalog 6 _ hnum valid511
end Section14Records_6_480_512

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0480_0512

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 384).take 128, section14RecordValid section14Catalog 6 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (6 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 6 r
  exact (all_of_interval_split P xs 384 448 512 (by decide) (by decide) (all_of_interval_split P xs 384 416 448 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_0384_0416 hnum) (Freiman.workReverse20260919_s0006_records_0416_0448 hnum)) (all_of_interval_split P xs 448 480 512 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_0448_0480 hnum) (Freiman.workReverse20260919_s0006_records_0480_0512 hnum)))

#print axioms solution
