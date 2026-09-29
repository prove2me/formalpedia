-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_3392_3456
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:30:42.752593+00:00
-- url     : https://prove2.me/submissions/1d68d80b-04e7-4144-ac11-4aa17be499a5

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3392_3424
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_3392_3424
private theorem valid3392 : RecordDataValid section14Catalog 6 (⟨226,(3),[5,6],[174],767⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨767,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],768⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3393 : RecordDataValid section14Catalog 6 (⟨226,(4),[1,2,5,6,13,14],[170],769⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨769,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],770⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3394 : RecordDataValid section14Catalog 6 (⟨226,(4),[5,6],[174],769⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨769,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],770⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3395 : RecordDataValid section14Catalog 6 (⟨226,(5),[1,2,5,6,13,14],[170],770⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨770,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],771⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3396 : RecordDataValid section14Catalog 6 (⟨226,(5),[5,6],[174],770⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨770,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],771⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3397 : RecordDataValid section14Catalog 6 (⟨226,(6),[1,2,5,6,13,14],[170],771⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨771,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],772⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3398 : RecordDataValid section14Catalog 6 (⟨226,(6),[5,6],[174],771⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨771,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],772⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3399 : RecordDataValid section14Catalog 6 (⟨226,(7),[1,2,5,6,13,14],[170],771⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨771,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],772⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3400 : RecordDataValid section14Catalog 6 (⟨226,(7),[5,6],[174],771⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨771,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],772⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3401 : RecordDataValid section14Catalog 6 (⟨226,(8),[1,2,5,6,13,14],[170],772⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨772,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],773⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3402 : RecordDataValid section14Catalog 6 (⟨226,(8),[5,6],[174],772⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨772,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],773⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3403 : RecordDataValid section14Catalog 6 (⟨226,(9),[1,2,5,6,13,14],[170],772⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨772,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],773⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3404 : RecordDataValid section14Catalog 6 (⟨226,(9),[5,6],[174],772⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨772,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],773⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3405 : RecordDataValid section14Catalog 6 (⟨227,(0),[1,2,5,6,13,14],[170],773⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨773,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],774⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3406 : RecordDataValid section14Catalog 6 (⟨227,(0),[5,6],[174],773⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨773,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],774⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3407 : RecordDataValid section14Catalog 6 (⟨227,(1),[1,2,5,6,13,14],[170],774⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨774,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],775⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3408 : RecordDataValid section14Catalog 6 (⟨227,(1),[5,6],[174],774⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨774,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],775⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3409 : RecordDataValid section14Catalog 6 (⟨227,(2),[1,2,5,6,13,14],[170],775⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨775,[1,2,3,5,6,7,10,11,13,14,15],776⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3410 : RecordDataValid section14Catalog 6 (⟨227,(2),[5,6],[174],1056⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1056,[3,5,6,7],1060⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3411 : RecordDataValid section14Catalog 6 (⟨227,(3),[1,2,5,6,13,14],[170],776⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨776,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],777⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3412 : RecordDataValid section14Catalog 6 (⟨227,(3),[5,6],[174],1057⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1057,[3,5,6,7],1061⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3413 : RecordDataValid section14Catalog 6 (⟨227,(4),[1,2,5,6,13,14],[170],775⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨775,[1,2,3,5,6,7,10,11,13,14,15],776⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3414 : RecordDataValid section14Catalog 6 (⟨227,(4),[5,6],[174],1056⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1056,[3,5,6,7],1060⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3415 : RecordDataValid section14Catalog 6 (⟨227,(5),[1,2,5,6,13,14],[170],773⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨773,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],774⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3416 : RecordDataValid section14Catalog 6 (⟨227,(5),[5,6],[174],773⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨773,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],774⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3417 : RecordDataValid section14Catalog 6 (⟨227,(6),[1,2,5,6,13,14],[170],774⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨774,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],775⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3418 : RecordDataValid section14Catalog 6 (⟨227,(6),[5,6],[174],774⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨774,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],775⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3419 : RecordDataValid section14Catalog 6 (⟨227,(7),[1,2,5,6,13,14],[170],775⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨775,[1,2,3,5,6,7,10,11,13,14,15],776⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3420 : RecordDataValid section14Catalog 6 (⟨227,(7),[5,6],[174],1056⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1056,[3,5,6,7],1060⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3421 : RecordDataValid section14Catalog 6 (⟨227,(8),[1,2,5,6,13,14],[170],776⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨776,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],777⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3422 : RecordDataValid section14Catalog 6 (⟨227,(8),[5,6],[174],1057⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1057,[3,5,6,7],1061⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3423 : RecordDataValid section14Catalog 6 (⟨227,(9),[1,2,5,6,13,14],[170],775⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨775,[1,2,3,5,6,7,10,11,13,14,15],776⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_3392_3424 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3392).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3392).take 32 = [⟨226,(3),[5,6],[174],767⟩,⟨226,(4),[1,2,5,6,13,14],[170],769⟩,⟨226,(4),[5,6],[174],769⟩,⟨226,(5),[1,2,5,6,13,14],[170],770⟩,⟨226,(5),[5,6],[174],770⟩,⟨226,(6),[1,2,5,6,13,14],[170],771⟩,⟨226,(6),[5,6],[174],771⟩,⟨226,(7),[1,2,5,6,13,14],[170],771⟩,⟨226,(7),[5,6],[174],771⟩,⟨226,(8),[1,2,5,6,13,14],[170],772⟩,⟨226,(8),[5,6],[174],772⟩,⟨226,(9),[1,2,5,6,13,14],[170],772⟩,⟨226,(9),[5,6],[174],772⟩,⟨227,(0),[1,2,5,6,13,14],[170],773⟩,⟨227,(0),[5,6],[174],773⟩,⟨227,(1),[1,2,5,6,13,14],[170],774⟩,⟨227,(1),[5,6],[174],774⟩,⟨227,(2),[1,2,5,6,13,14],[170],775⟩,⟨227,(2),[5,6],[174],1056⟩,⟨227,(3),[1,2,5,6,13,14],[170],776⟩,⟨227,(3),[5,6],[174],1057⟩,⟨227,(4),[1,2,5,6,13,14],[170],775⟩,⟨227,(4),[5,6],[174],1056⟩,⟨227,(5),[1,2,5,6,13,14],[170],773⟩,⟨227,(5),[5,6],[174],773⟩,⟨227,(6),[1,2,5,6,13,14],[170],774⟩,⟨227,(6),[5,6],[174],774⟩,⟨227,(7),[1,2,5,6,13,14],[170],775⟩,⟨227,(7),[5,6],[174],1056⟩,⟨227,(8),[1,2,5,6,13,14],[170],776⟩,⟨227,(8),[5,6],[174],1057⟩,⟨227,(9),[1,2,5,6,13,14],[170],775⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3392
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3393
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3394
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3395
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3396
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3397
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3398
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3399
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3400
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3401
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3402
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3403
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3404
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3405
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3406
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3407
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3408
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3409
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3410
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3411
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3412
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3413
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3414
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3415
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3416
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3417
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3418
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3419
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3420
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3421
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3422
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3423
end Section14Records_6_3392_3424

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3392_3424


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3424_3456
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_3424_3456
private theorem valid3424 : RecordDataValid section14Catalog 6 (⟨227,(9),[5,6],[174],1056⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1056,[3,5,6,7],1060⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3425 : RecordDataValid section14Catalog 6 (⟨227,(10),[1,2,5,6,13,14],[170],777⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨777,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],778⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3426 : RecordDataValid section14Catalog 6 (⟨227,(10),[5,6],[174],777⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨777,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],778⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3427 : RecordDataValid section14Catalog 6 (⟨227,(11),[1,2,5,6,13,14],[170],778⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨778,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],779⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3428 : RecordDataValid section14Catalog 6 (⟨227,(11),[5,6],[174],778⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨778,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],779⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3429 : RecordDataValid section14Catalog 6 (⟨227,(12),[1,2,5,6,13,14],[170],779⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨779,[1,2,3,5,6,7,10,11,13,14,15],780⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3430 : RecordDataValid section14Catalog 6 (⟨227,(12),[5,6],[174],1058⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1058,[3,5,6,7],1062⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3431 : RecordDataValid section14Catalog 6 (⟨227,(13),[1,2,5,6,13,14],[170],780⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨780,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],781⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3432 : RecordDataValid section14Catalog 6 (⟨227,(13),[5,6],[174],1059⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1059,[3,5,6,7],1063⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3433 : RecordDataValid section14Catalog 6 (⟨227,(14),[1,2,5,6,13,14],[170],779⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨779,[1,2,3,5,6,7,10,11,13,14,15],780⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3434 : RecordDataValid section14Catalog 6 (⟨227,(14),[5,6],[174],1058⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1058,[3,5,6,7],1062⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3435 : RecordDataValid section14Catalog 6 (⟨227,(15),[1,2,5,6,13,14],[170],781⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨781,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],782⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3436 : RecordDataValid section14Catalog 6 (⟨227,(15),[5,6],[174],781⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨781,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],782⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3437 : RecordDataValid section14Catalog 6 (⟨227,(16),[1,2,5,6,13,14],[170],782⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨782,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],783⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3438 : RecordDataValid section14Catalog 6 (⟨227,(16),[5,6],[174],782⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨782,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],783⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3439 : RecordDataValid section14Catalog 6 (⟨227,(17),[1,2,5,6,13,14],[170],783⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨783,[1,2,3,5,6,7,10,11,13,14,15],784⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3440 : RecordDataValid section14Catalog 6 (⟨227,(17),[5,6],[174],1060⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1060,[3,5,6,7],1064⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3441 : RecordDataValid section14Catalog 6 (⟨227,(18),[1,2,5,6,13,14],[170],784⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨784,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],785⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3442 : RecordDataValid section14Catalog 6 (⟨227,(18),[5,6],[174],1060⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1060,[3,5,6,7],1064⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3443 : RecordDataValid section14Catalog 6 (⟨227,(19),[1,2,5,6,13,14],[170],783⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨783,[1,2,3,5,6,7,10,11,13,14,15],784⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3444 : RecordDataValid section14Catalog 6 (⟨227,(19),[5,6],[174],1060⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1060,[3,5,6,7],1064⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3445 : RecordDataValid section14Catalog 6 (⟨227,(20),[1,2,5,6,13,14],[170],785⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨785,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],786⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3446 : RecordDataValid section14Catalog 6 (⟨227,(20),[5,6],[174],785⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨785,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],786⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3447 : RecordDataValid section14Catalog 6 (⟨227,(21),[1,2,5,6,13,14],[170],786⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨786,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],787⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3448 : RecordDataValid section14Catalog 6 (⟨227,(21),[5,6],[174],786⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨786,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],787⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3449 : RecordDataValid section14Catalog 6 (⟨227,(22),[1,2,5,6,13,14],[170],787⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨787,[1,2,3,5,6,7,10,11,13,14,15],788⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3450 : RecordDataValid section14Catalog 6 (⟨227,(22),[5,6],[174],1061⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1061,[3,5,6,7],1065⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3451 : RecordDataValid section14Catalog 6 (⟨227,(23),[1,2,5,6,13,14],[170],788⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨788,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],789⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3452 : RecordDataValid section14Catalog 6 (⟨227,(23),[5,6],[174],1062⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1062,[3,5,6,7],1066⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3453 : RecordDataValid section14Catalog 6 (⟨227,(24),[1,2,5,6,13,14],[170],787⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨787,[1,2,3,5,6,7,10,11,13,14,15],788⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3454 : RecordDataValid section14Catalog 6 (⟨227,(24),[5,6],[174],1061⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1061,[3,5,6,7],1065⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3455 : RecordDataValid section14Catalog 6 (⟨228,(0),[1,2,5,6,13,14],[170],789⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨789,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],790⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_3424_3456 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3424).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3424).take 32 = [⟨227,(9),[5,6],[174],1056⟩,⟨227,(10),[1,2,5,6,13,14],[170],777⟩,⟨227,(10),[5,6],[174],777⟩,⟨227,(11),[1,2,5,6,13,14],[170],778⟩,⟨227,(11),[5,6],[174],778⟩,⟨227,(12),[1,2,5,6,13,14],[170],779⟩,⟨227,(12),[5,6],[174],1058⟩,⟨227,(13),[1,2,5,6,13,14],[170],780⟩,⟨227,(13),[5,6],[174],1059⟩,⟨227,(14),[1,2,5,6,13,14],[170],779⟩,⟨227,(14),[5,6],[174],1058⟩,⟨227,(15),[1,2,5,6,13,14],[170],781⟩,⟨227,(15),[5,6],[174],781⟩,⟨227,(16),[1,2,5,6,13,14],[170],782⟩,⟨227,(16),[5,6],[174],782⟩,⟨227,(17),[1,2,5,6,13,14],[170],783⟩,⟨227,(17),[5,6],[174],1060⟩,⟨227,(18),[1,2,5,6,13,14],[170],784⟩,⟨227,(18),[5,6],[174],1060⟩,⟨227,(19),[1,2,5,6,13,14],[170],783⟩,⟨227,(19),[5,6],[174],1060⟩,⟨227,(20),[1,2,5,6,13,14],[170],785⟩,⟨227,(20),[5,6],[174],785⟩,⟨227,(21),[1,2,5,6,13,14],[170],786⟩,⟨227,(21),[5,6],[174],786⟩,⟨227,(22),[1,2,5,6,13,14],[170],787⟩,⟨227,(22),[5,6],[174],1061⟩,⟨227,(23),[1,2,5,6,13,14],[170],788⟩,⟨227,(23),[5,6],[174],1062⟩,⟨227,(24),[1,2,5,6,13,14],[170],787⟩,⟨227,(24),[5,6],[174],1061⟩,⟨228,(0),[1,2,5,6,13,14],[170],789⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3424
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3425
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3426
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3427
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3428
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3429
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3430
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3431
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3432
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3433
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3434
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3435
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3436
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3437
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3438
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3439
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3440
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3441
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3442
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3443
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3444
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3445
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3446
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3447
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3448
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3449
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3450
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3451
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3452
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3453
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3454
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3455
end Section14Records_6_3424_3456

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3424_3456

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3392).take 64, section14RecordValid section14Catalog 6 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (6 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 6 r
  exact (all_of_interval_split P xs 3392 3424 3456 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_3392_3424 hnum) (Freiman.workReverse20260919_s0006_records_3424_3456 hnum))

#print axioms solution
