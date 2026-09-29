-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_0512_0640
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:10:47.969927+00:00
-- url     : https://prove2.me/submissions/32e68296-3086-4569-9ac2-97223b4dca15

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_0512_0544
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_512_544
private theorem valid512 : RecordDataValid section14Catalog 5 (⟨23,(19),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid513 : RecordDataValid section14Catalog 5 (⟨23,(19),[1,5],[134],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid514 : RecordDataValid section14Catalog 5 (⟨23,(19),[1,5,13],[135],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid515 : RecordDataValid section14Catalog 5 (⟨23,(20),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid516 : RecordDataValid section14Catalog 5 (⟨23,(20),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid517 : RecordDataValid section14Catalog 5 (⟨23,(20),[1,5],[134],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid518 : RecordDataValid section14Catalog 5 (⟨23,(20),[1,5,13],[135],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid519 : RecordDataValid section14Catalog 5 (⟨23,(21),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid520 : RecordDataValid section14Catalog 5 (⟨23,(21),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid521 : RecordDataValid section14Catalog 5 (⟨23,(21),[1,5],[134],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid522 : RecordDataValid section14Catalog 5 (⟨23,(21),[1,5,13],[135],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid523 : RecordDataValid section14Catalog 5 (⟨23,(22),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid524 : RecordDataValid section14Catalog 5 (⟨23,(22),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid525 : RecordDataValid section14Catalog 5 (⟨23,(22),[1,5],[134],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid526 : RecordDataValid section14Catalog 5 (⟨23,(22),[1,5,13],[135],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid527 : RecordDataValid section14Catalog 5 (⟨23,(23),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid528 : RecordDataValid section14Catalog 5 (⟨23,(23),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid529 : RecordDataValid section14Catalog 5 (⟨23,(23),[1,5],[134],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid530 : RecordDataValid section14Catalog 5 (⟨23,(23),[1,5,13],[135],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid531 : RecordDataValid section14Catalog 5 (⟨23,(24),[1,2,5,6],[130],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid532 : RecordDataValid section14Catalog 5 (⟨23,(24),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid533 : RecordDataValid section14Catalog 5 (⟨23,(24),[1,5],[134],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid534 : RecordDataValid section14Catalog 5 (⟨23,(24),[1,5,13],[135],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid535 : RecordDataValid section14Catalog 5 (⟨25,(0),[1,2,5,6],[130],80⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨80,[1,2,5,6,9,10,12,13,14],80⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid536 : RecordDataValid section14Catalog 5 (⟨25,(0),[1,2,5,6,13,14],[146],145⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨145,[1,2,3,5,6,7,13,14,15],145⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid537 : RecordDataValid section14Catalog 5 (⟨25,(0),[1,2,5,6,13,14],[150],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid538 : RecordDataValid section14Catalog 5 (⟨25,(0),[1,5],[134],80⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨80,[1,2,5,6,9,10,12,13,14],80⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid539 : RecordDataValid section14Catalog 5 (⟨25,(0),[5],[135],167⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨167,[1,2,5,6,9,10,13,14],167⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid540 : RecordDataValid section14Catalog 5 (⟨25,(0),[5,6],[131],167⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨167,[1,2,5,6,9,10,13,14],167⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid541 : RecordDataValid section14Catalog 5 (⟨25,(1),[1,2,5,6],[130],81⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨81,[1,2,5,6,9,10,12,13,14],81⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid542 : RecordDataValid section14Catalog 5 (⟨25,(1),[1,2,5,6,13,14],[146],146⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨146,[1,2,3,5,6,7,13,14,15],146⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid543 : RecordDataValid section14Catalog 5 (⟨25,(1),[1,5],[134],81⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨81,[1,2,5,6,9,10,12,13,14],81⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_0512_0544 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 512).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 512).take 32 = [⟨23,(19),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(19),[1,5],[134],2⟩,⟨23,(19),[1,5,13],[135],2⟩,⟨23,(20),[1,2,5,6],[130],2⟩,⟨23,(20),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(20),[1,5],[134],2⟩,⟨23,(20),[1,5,13],[135],2⟩,⟨23,(21),[1,2,5,6],[130],2⟩,⟨23,(21),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(21),[1,5],[134],2⟩,⟨23,(21),[1,5,13],[135],2⟩,⟨23,(22),[1,2,5,6],[130],2⟩,⟨23,(22),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(22),[1,5],[134],2⟩,⟨23,(22),[1,5,13],[135],2⟩,⟨23,(23),[1,2,5,6],[130],2⟩,⟨23,(23),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(23),[1,5],[134],2⟩,⟨23,(23),[1,5,13],[135],2⟩,⟨23,(24),[1,2,5,6],[130],2⟩,⟨23,(24),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(24),[1,5],[134],2⟩,⟨23,(24),[1,5,13],[135],2⟩,⟨25,(0),[1,2,5,6],[130],80⟩,⟨25,(0),[1,2,5,6,13,14],[146],145⟩,⟨25,(0),[1,2,5,6,13,14],[150],189⟩,⟨25,(0),[1,5],[134],80⟩,⟨25,(0),[5],[135],167⟩,⟨25,(0),[5,6],[131],167⟩,⟨25,(1),[1,2,5,6],[130],81⟩,⟨25,(1),[1,2,5,6,13,14],[146],146⟩,⟨25,(1),[1,5],[134],81⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid512
  · exact recordValid_of_data section14Catalog 5 _ hnum valid513
  · exact recordValid_of_data section14Catalog 5 _ hnum valid514
  · exact recordValid_of_data section14Catalog 5 _ hnum valid515
  · exact recordValid_of_data section14Catalog 5 _ hnum valid516
  · exact recordValid_of_data section14Catalog 5 _ hnum valid517
  · exact recordValid_of_data section14Catalog 5 _ hnum valid518
  · exact recordValid_of_data section14Catalog 5 _ hnum valid519
  · exact recordValid_of_data section14Catalog 5 _ hnum valid520
  · exact recordValid_of_data section14Catalog 5 _ hnum valid521
  · exact recordValid_of_data section14Catalog 5 _ hnum valid522
  · exact recordValid_of_data section14Catalog 5 _ hnum valid523
  · exact recordValid_of_data section14Catalog 5 _ hnum valid524
  · exact recordValid_of_data section14Catalog 5 _ hnum valid525
  · exact recordValid_of_data section14Catalog 5 _ hnum valid526
  · exact recordValid_of_data section14Catalog 5 _ hnum valid527
  · exact recordValid_of_data section14Catalog 5 _ hnum valid528
  · exact recordValid_of_data section14Catalog 5 _ hnum valid529
  · exact recordValid_of_data section14Catalog 5 _ hnum valid530
  · exact recordValid_of_data section14Catalog 5 _ hnum valid531
  · exact recordValid_of_data section14Catalog 5 _ hnum valid532
  · exact recordValid_of_data section14Catalog 5 _ hnum valid533
  · exact recordValid_of_data section14Catalog 5 _ hnum valid534
  · exact recordValid_of_data section14Catalog 5 _ hnum valid535
  · exact recordValid_of_data section14Catalog 5 _ hnum valid536
  · exact recordValid_of_data section14Catalog 5 _ hnum valid537
  · exact recordValid_of_data section14Catalog 5 _ hnum valid538
  · exact recordValid_of_data section14Catalog 5 _ hnum valid539
  · exact recordValid_of_data section14Catalog 5 _ hnum valid540
  · exact recordValid_of_data section14Catalog 5 _ hnum valid541
  · exact recordValid_of_data section14Catalog 5 _ hnum valid542
  · exact recordValid_of_data section14Catalog 5 _ hnum valid543
end Section14Records_5_512_544

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_0512_0544


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_0544_0576
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_544_576
private theorem valid544 : RecordDataValid section14Catalog 5 (⟨25,(1),[5],[135],168⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨168,[1,2,5,6,9,10,13,14],168⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid545 : RecordDataValid section14Catalog 5 (⟨25,(1),[5,6],[131],168⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨168,[1,2,5,6,9,10,13,14],168⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid546 : RecordDataValid section14Catalog 5 (⟨25,(1),[5,6],[150],216⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨216,[1,2,3,5,6,7,8,9,10,11,12,13,14,15],216⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid547 : RecordDataValid section14Catalog 5 (⟨25,(2),[1,2,5,6],[130],80⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨80,[1,2,5,6,9,10,12,13,14],80⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid548 : RecordDataValid section14Catalog 5 (⟨25,(2),[1,2,5,6,13,14],[146],145⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨145,[1,2,3,5,6,7,13,14,15],145⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid549 : RecordDataValid section14Catalog 5 (⟨25,(2),[1,5],[134],80⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨80,[1,2,5,6,9,10,12,13,14],80⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid550 : RecordDataValid section14Catalog 5 (⟨25,(2),[5],[135],167⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨167,[1,2,5,6,9,10,13,14],167⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid551 : RecordDataValid section14Catalog 5 (⟨25,(2),[5,6],[131],167⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨167,[1,2,5,6,9,10,13,14],167⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid552 : RecordDataValid section14Catalog 5 (⟨25,(2),[5,6],[150],217⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨217,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],217⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid553 : RecordDataValid section14Catalog 5 (⟨25,(3),[1,2,5,6],[130],82⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨82,[1,2,5,6,9,10,12,13,14],82⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid554 : RecordDataValid section14Catalog 5 (⟨25,(3),[1,2,5,6,13,14],[146],147⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨147,[1,2,3,5,6,7,13,14,15],147⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid555 : RecordDataValid section14Catalog 5 (⟨25,(3),[1,5],[134],82⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨82,[1,2,5,6,9,10,12,13,14],82⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid556 : RecordDataValid section14Catalog 5 (⟨25,(3),[5],[135],169⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨169,[1,2,5,6,9,10,13,14],169⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid557 : RecordDataValid section14Catalog 5 (⟨25,(3),[5,6],[131],169⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨169,[1,2,5,6,9,10,13,14],169⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid558 : RecordDataValid section14Catalog 5 (⟨25,(3),[5,6],[150],218⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨218,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],218⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid559 : RecordDataValid section14Catalog 5 (⟨25,(4),[1,2,5,6],[130],83⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨83,[1,2,5,6,9,10,12,13,14],83⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid560 : RecordDataValid section14Catalog 5 (⟨25,(4),[1,2,5,6,13,14],[146],148⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨148,[1,2,3,5,6,7,13,14,15],148⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid561 : RecordDataValid section14Catalog 5 (⟨25,(4),[1,5],[134],83⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨83,[1,2,5,6,9,10,12,13,14],83⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid562 : RecordDataValid section14Catalog 5 (⟨25,(4),[5],[135],170⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨170,[1,2,5,6,9,10,13,14],170⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid563 : RecordDataValid section14Catalog 5 (⟨25,(4),[5,6],[131],170⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨170,[1,2,5,6,9,10,13,14],170⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid564 : RecordDataValid section14Catalog 5 (⟨25,(4),[5,6],[150],219⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨219,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],219⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid565 : RecordDataValid section14Catalog 5 (⟨25,(5),[1,2,5,6],[130],80⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨80,[1,2,5,6,9,10,12,13,14],80⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid566 : RecordDataValid section14Catalog 5 (⟨25,(5),[1,2,5,6,13,14],[146],145⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨145,[1,2,3,5,6,7,13,14,15],145⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid567 : RecordDataValid section14Catalog 5 (⟨25,(5),[1,2,5,6,13,14],[150],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid568 : RecordDataValid section14Catalog 5 (⟨25,(5),[1,5],[134],80⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨80,[1,2,5,6,9,10,12,13,14],80⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid569 : RecordDataValid section14Catalog 5 (⟨25,(5),[5],[135],167⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨167,[1,2,5,6,9,10,13,14],167⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid570 : RecordDataValid section14Catalog 5 (⟨25,(5),[5,6],[131],167⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨167,[1,2,5,6,9,10,13,14],167⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid571 : RecordDataValid section14Catalog 5 (⟨25,(6),[1,2,5,6],[130],81⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨81,[1,2,5,6,9,10,12,13,14],81⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid572 : RecordDataValid section14Catalog 5 (⟨25,(6),[1,2,5,6,13,14],[146],146⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨146,[1,2,3,5,6,7,13,14,15],146⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid573 : RecordDataValid section14Catalog 5 (⟨25,(6),[1,5],[134],81⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨81,[1,2,5,6,9,10,12,13,14],81⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid574 : RecordDataValid section14Catalog 5 (⟨25,(6),[5],[135],168⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨168,[1,2,5,6,9,10,13,14],168⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid575 : RecordDataValid section14Catalog 5 (⟨25,(6),[5,6],[131],168⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨168,[1,2,5,6,9,10,13,14],168⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_0544_0576 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 544).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 544).take 32 = [⟨25,(1),[5],[135],168⟩,⟨25,(1),[5,6],[131],168⟩,⟨25,(1),[5,6],[150],216⟩,⟨25,(2),[1,2,5,6],[130],80⟩,⟨25,(2),[1,2,5,6,13,14],[146],145⟩,⟨25,(2),[1,5],[134],80⟩,⟨25,(2),[5],[135],167⟩,⟨25,(2),[5,6],[131],167⟩,⟨25,(2),[5,6],[150],217⟩,⟨25,(3),[1,2,5,6],[130],82⟩,⟨25,(3),[1,2,5,6,13,14],[146],147⟩,⟨25,(3),[1,5],[134],82⟩,⟨25,(3),[5],[135],169⟩,⟨25,(3),[5,6],[131],169⟩,⟨25,(3),[5,6],[150],218⟩,⟨25,(4),[1,2,5,6],[130],83⟩,⟨25,(4),[1,2,5,6,13,14],[146],148⟩,⟨25,(4),[1,5],[134],83⟩,⟨25,(4),[5],[135],170⟩,⟨25,(4),[5,6],[131],170⟩,⟨25,(4),[5,6],[150],219⟩,⟨25,(5),[1,2,5,6],[130],80⟩,⟨25,(5),[1,2,5,6,13,14],[146],145⟩,⟨25,(5),[1,2,5,6,13,14],[150],189⟩,⟨25,(5),[1,5],[134],80⟩,⟨25,(5),[5],[135],167⟩,⟨25,(5),[5,6],[131],167⟩,⟨25,(6),[1,2,5,6],[130],81⟩,⟨25,(6),[1,2,5,6,13,14],[146],146⟩,⟨25,(6),[1,5],[134],81⟩,⟨25,(6),[5],[135],168⟩,⟨25,(6),[5,6],[131],168⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid544
  · exact recordValid_of_data section14Catalog 5 _ hnum valid545
  · exact recordValid_of_data section14Catalog 5 _ hnum valid546
  · exact recordValid_of_data section14Catalog 5 _ hnum valid547
  · exact recordValid_of_data section14Catalog 5 _ hnum valid548
  · exact recordValid_of_data section14Catalog 5 _ hnum valid549
  · exact recordValid_of_data section14Catalog 5 _ hnum valid550
  · exact recordValid_of_data section14Catalog 5 _ hnum valid551
  · exact recordValid_of_data section14Catalog 5 _ hnum valid552
  · exact recordValid_of_data section14Catalog 5 _ hnum valid553
  · exact recordValid_of_data section14Catalog 5 _ hnum valid554
  · exact recordValid_of_data section14Catalog 5 _ hnum valid555
  · exact recordValid_of_data section14Catalog 5 _ hnum valid556
  · exact recordValid_of_data section14Catalog 5 _ hnum valid557
  · exact recordValid_of_data section14Catalog 5 _ hnum valid558
  · exact recordValid_of_data section14Catalog 5 _ hnum valid559
  · exact recordValid_of_data section14Catalog 5 _ hnum valid560
  · exact recordValid_of_data section14Catalog 5 _ hnum valid561
  · exact recordValid_of_data section14Catalog 5 _ hnum valid562
  · exact recordValid_of_data section14Catalog 5 _ hnum valid563
  · exact recordValid_of_data section14Catalog 5 _ hnum valid564
  · exact recordValid_of_data section14Catalog 5 _ hnum valid565
  · exact recordValid_of_data section14Catalog 5 _ hnum valid566
  · exact recordValid_of_data section14Catalog 5 _ hnum valid567
  · exact recordValid_of_data section14Catalog 5 _ hnum valid568
  · exact recordValid_of_data section14Catalog 5 _ hnum valid569
  · exact recordValid_of_data section14Catalog 5 _ hnum valid570
  · exact recordValid_of_data section14Catalog 5 _ hnum valid571
  · exact recordValid_of_data section14Catalog 5 _ hnum valid572
  · exact recordValid_of_data section14Catalog 5 _ hnum valid573
  · exact recordValid_of_data section14Catalog 5 _ hnum valid574
  · exact recordValid_of_data section14Catalog 5 _ hnum valid575
end Section14Records_5_544_576

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_0544_0576


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_0576_0608
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_576_608
private theorem valid576 : RecordDataValid section14Catalog 5 (⟨25,(6),[5,6],[150],216⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨216,[1,2,3,5,6,7,8,9,10,11,12,13,14,15],216⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid577 : RecordDataValid section14Catalog 5 (⟨25,(7),[1,2,5,6],[130],80⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨80,[1,2,5,6,9,10,12,13,14],80⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid578 : RecordDataValid section14Catalog 5 (⟨25,(7),[1,2,5,6,13,14],[146],145⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨145,[1,2,3,5,6,7,13,14,15],145⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid579 : RecordDataValid section14Catalog 5 (⟨25,(7),[1,5],[134],80⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨80,[1,2,5,6,9,10,12,13,14],80⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid580 : RecordDataValid section14Catalog 5 (⟨25,(7),[5],[135],167⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨167,[1,2,5,6,9,10,13,14],167⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid581 : RecordDataValid section14Catalog 5 (⟨25,(7),[5,6],[131],167⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨167,[1,2,5,6,9,10,13,14],167⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid582 : RecordDataValid section14Catalog 5 (⟨25,(7),[5,6],[150],217⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨217,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],217⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid583 : RecordDataValid section14Catalog 5 (⟨25,(8),[1,2,5,6],[130],82⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨82,[1,2,5,6,9,10,12,13,14],82⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid584 : RecordDataValid section14Catalog 5 (⟨25,(8),[1,2,5,6,13,14],[146],147⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨147,[1,2,3,5,6,7,13,14,15],147⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid585 : RecordDataValid section14Catalog 5 (⟨25,(8),[1,5],[134],82⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨82,[1,2,5,6,9,10,12,13,14],82⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid586 : RecordDataValid section14Catalog 5 (⟨25,(8),[5],[135],169⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨169,[1,2,5,6,9,10,13,14],169⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid587 : RecordDataValid section14Catalog 5 (⟨25,(8),[5,6],[131],169⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨169,[1,2,5,6,9,10,13,14],169⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid588 : RecordDataValid section14Catalog 5 (⟨25,(8),[5,6],[150],218⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨218,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],218⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid589 : RecordDataValid section14Catalog 5 (⟨25,(9),[1,2,5,6],[130],83⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨83,[1,2,5,6,9,10,12,13,14],83⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid590 : RecordDataValid section14Catalog 5 (⟨25,(9),[1,2,5,6,13,14],[146],148⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨148,[1,2,3,5,6,7,13,14,15],148⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid591 : RecordDataValid section14Catalog 5 (⟨25,(9),[1,5],[134],83⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨83,[1,2,5,6,9,10,12,13,14],83⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid592 : RecordDataValid section14Catalog 5 (⟨25,(9),[5],[135],170⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨170,[1,2,5,6,9,10,13,14],170⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid593 : RecordDataValid section14Catalog 5 (⟨25,(9),[5,6],[131],170⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨170,[1,2,5,6,9,10,13,14],170⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid594 : RecordDataValid section14Catalog 5 (⟨25,(9),[5,6],[150],219⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨219,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],219⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid595 : RecordDataValid section14Catalog 5 (⟨25,(10),[1,2,5,6],[130],84⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid596 : RecordDataValid section14Catalog 5 (⟨25,(10),[1,2,5,6,13,14],[146],149⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨149,[1,2,3,5,6,7,13,14,15],149⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid597 : RecordDataValid section14Catalog 5 (⟨25,(10),[1,2,5,6,13,14],[150],194⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨194,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],194⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid598 : RecordDataValid section14Catalog 5 (⟨25,(10),[1,5],[134],84⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid599 : RecordDataValid section14Catalog 5 (⟨25,(10),[5],[135],171⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨171,[1,2,5,6,9,10,13,14],171⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid600 : RecordDataValid section14Catalog 5 (⟨25,(10),[5,6],[131],171⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨171,[1,2,5,6,9,10,13,14],171⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid601 : RecordDataValid section14Catalog 5 (⟨25,(11),[1,2,5,6],[130],84⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid602 : RecordDataValid section14Catalog 5 (⟨25,(11),[1,2,5,6,13,14],[146],149⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨149,[1,2,3,5,6,7,13,14,15],149⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid603 : RecordDataValid section14Catalog 5 (⟨25,(11),[1,5],[134],84⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid604 : RecordDataValid section14Catalog 5 (⟨25,(11),[5],[135],171⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨171,[1,2,5,6,9,10,13,14],171⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid605 : RecordDataValid section14Catalog 5 (⟨25,(11),[5,6],[131],171⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨171,[1,2,5,6,9,10,13,14],171⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid606 : RecordDataValid section14Catalog 5 (⟨25,(11),[5,6],[150],220⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨220,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],220⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid607 : RecordDataValid section14Catalog 5 (⟨25,(12),[1,2,5,6],[130],84⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_0576_0608 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 576).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 576).take 32 = [⟨25,(6),[5,6],[150],216⟩,⟨25,(7),[1,2,5,6],[130],80⟩,⟨25,(7),[1,2,5,6,13,14],[146],145⟩,⟨25,(7),[1,5],[134],80⟩,⟨25,(7),[5],[135],167⟩,⟨25,(7),[5,6],[131],167⟩,⟨25,(7),[5,6],[150],217⟩,⟨25,(8),[1,2,5,6],[130],82⟩,⟨25,(8),[1,2,5,6,13,14],[146],147⟩,⟨25,(8),[1,5],[134],82⟩,⟨25,(8),[5],[135],169⟩,⟨25,(8),[5,6],[131],169⟩,⟨25,(8),[5,6],[150],218⟩,⟨25,(9),[1,2,5,6],[130],83⟩,⟨25,(9),[1,2,5,6,13,14],[146],148⟩,⟨25,(9),[1,5],[134],83⟩,⟨25,(9),[5],[135],170⟩,⟨25,(9),[5,6],[131],170⟩,⟨25,(9),[5,6],[150],219⟩,⟨25,(10),[1,2,5,6],[130],84⟩,⟨25,(10),[1,2,5,6,13,14],[146],149⟩,⟨25,(10),[1,2,5,6,13,14],[150],194⟩,⟨25,(10),[1,5],[134],84⟩,⟨25,(10),[5],[135],171⟩,⟨25,(10),[5,6],[131],171⟩,⟨25,(11),[1,2,5,6],[130],84⟩,⟨25,(11),[1,2,5,6,13,14],[146],149⟩,⟨25,(11),[1,5],[134],84⟩,⟨25,(11),[5],[135],171⟩,⟨25,(11),[5,6],[131],171⟩,⟨25,(11),[5,6],[150],220⟩,⟨25,(12),[1,2,5,6],[130],84⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid576
  · exact recordValid_of_data section14Catalog 5 _ hnum valid577
  · exact recordValid_of_data section14Catalog 5 _ hnum valid578
  · exact recordValid_of_data section14Catalog 5 _ hnum valid579
  · exact recordValid_of_data section14Catalog 5 _ hnum valid580
  · exact recordValid_of_data section14Catalog 5 _ hnum valid581
  · exact recordValid_of_data section14Catalog 5 _ hnum valid582
  · exact recordValid_of_data section14Catalog 5 _ hnum valid583
  · exact recordValid_of_data section14Catalog 5 _ hnum valid584
  · exact recordValid_of_data section14Catalog 5 _ hnum valid585
  · exact recordValid_of_data section14Catalog 5 _ hnum valid586
  · exact recordValid_of_data section14Catalog 5 _ hnum valid587
  · exact recordValid_of_data section14Catalog 5 _ hnum valid588
  · exact recordValid_of_data section14Catalog 5 _ hnum valid589
  · exact recordValid_of_data section14Catalog 5 _ hnum valid590
  · exact recordValid_of_data section14Catalog 5 _ hnum valid591
  · exact recordValid_of_data section14Catalog 5 _ hnum valid592
  · exact recordValid_of_data section14Catalog 5 _ hnum valid593
  · exact recordValid_of_data section14Catalog 5 _ hnum valid594
  · exact recordValid_of_data section14Catalog 5 _ hnum valid595
  · exact recordValid_of_data section14Catalog 5 _ hnum valid596
  · exact recordValid_of_data section14Catalog 5 _ hnum valid597
  · exact recordValid_of_data section14Catalog 5 _ hnum valid598
  · exact recordValid_of_data section14Catalog 5 _ hnum valid599
  · exact recordValid_of_data section14Catalog 5 _ hnum valid600
  · exact recordValid_of_data section14Catalog 5 _ hnum valid601
  · exact recordValid_of_data section14Catalog 5 _ hnum valid602
  · exact recordValid_of_data section14Catalog 5 _ hnum valid603
  · exact recordValid_of_data section14Catalog 5 _ hnum valid604
  · exact recordValid_of_data section14Catalog 5 _ hnum valid605
  · exact recordValid_of_data section14Catalog 5 _ hnum valid606
  · exact recordValid_of_data section14Catalog 5 _ hnum valid607
end Section14Records_5_576_608

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_0576_0608


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_0608_0640
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_608_640
private theorem valid608 : RecordDataValid section14Catalog 5 (⟨25,(12),[1,2,5,6,13,14],[146],149⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨149,[1,2,3,5,6,7,13,14,15],149⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid609 : RecordDataValid section14Catalog 5 (⟨25,(12),[1,5],[134],84⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid610 : RecordDataValid section14Catalog 5 (⟨25,(12),[5],[135],171⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨171,[1,2,5,6,9,10,13,14],171⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid611 : RecordDataValid section14Catalog 5 (⟨25,(12),[5,6],[131],171⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨171,[1,2,5,6,9,10,13,14],171⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid612 : RecordDataValid section14Catalog 5 (⟨25,(12),[5,6],[150],220⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨220,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],220⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid613 : RecordDataValid section14Catalog 5 (⟨25,(13),[1,2,5,6],[130],84⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid614 : RecordDataValid section14Catalog 5 (⟨25,(13),[1,2,5,6,13,14],[146],149⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨149,[1,2,3,5,6,7,13,14,15],149⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid615 : RecordDataValid section14Catalog 5 (⟨25,(13),[1,5],[134],84⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid616 : RecordDataValid section14Catalog 5 (⟨25,(13),[5],[135],171⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨171,[1,2,5,6,9,10,13,14],171⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid617 : RecordDataValid section14Catalog 5 (⟨25,(13),[5,6],[131],171⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨171,[1,2,5,6,9,10,13,14],171⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid618 : RecordDataValid section14Catalog 5 (⟨25,(13),[5,6],[150],220⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨220,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],220⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid619 : RecordDataValid section14Catalog 5 (⟨25,(14),[1,2,5,6],[130],83⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨83,[1,2,5,6,9,10,12,13,14],83⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid620 : RecordDataValid section14Catalog 5 (⟨25,(14),[1,2,5,6,13,14],[146],148⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨148,[1,2,3,5,6,7,13,14,15],148⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid621 : RecordDataValid section14Catalog 5 (⟨25,(14),[1,5],[134],83⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨83,[1,2,5,6,9,10,12,13,14],83⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid622 : RecordDataValid section14Catalog 5 (⟨25,(14),[5],[135],170⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨170,[1,2,5,6,9,10,13,14],170⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid623 : RecordDataValid section14Catalog 5 (⟨25,(14),[5,6],[131],170⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨170,[1,2,5,6,9,10,13,14],170⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid624 : RecordDataValid section14Catalog 5 (⟨25,(14),[5,6],[150],219⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨219,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],219⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid625 : RecordDataValid section14Catalog 5 (⟨25,(15),[1,2,5,6],[130],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid626 : RecordDataValid section14Catalog 5 (⟨25,(15),[1,2,5,6,13,14],[146],150⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨150,[1,2,3,5,6,7,13,14,15],150⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid627 : RecordDataValid section14Catalog 5 (⟨25,(15),[1,2,5,6,13,14],[150],196⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨196,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],196⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid628 : RecordDataValid section14Catalog 5 (⟨25,(15),[1,5],[134],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid629 : RecordDataValid section14Catalog 5 (⟨25,(15),[5],[135],172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨172,[1,2,5,6,9,10,13,14],172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid630 : RecordDataValid section14Catalog 5 (⟨25,(15),[5,6],[131],172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨172,[1,2,5,6,9,10,13,14],172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid631 : RecordDataValid section14Catalog 5 (⟨25,(16),[1,2,5,6],[130],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid632 : RecordDataValid section14Catalog 5 (⟨25,(16),[1,2,5,6,13,14],[146],150⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨150,[1,2,3,5,6,7,13,14,15],150⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid633 : RecordDataValid section14Catalog 5 (⟨25,(16),[1,5],[134],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid634 : RecordDataValid section14Catalog 5 (⟨25,(16),[5],[135],172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨172,[1,2,5,6,9,10,13,14],172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid635 : RecordDataValid section14Catalog 5 (⟨25,(16),[5,6],[131],172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨172,[1,2,5,6,9,10,13,14],172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid636 : RecordDataValid section14Catalog 5 (⟨25,(16),[5,6],[150],221⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨221,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],221⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid637 : RecordDataValid section14Catalog 5 (⟨25,(17),[1,2,5,6],[130],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid638 : RecordDataValid section14Catalog 5 (⟨25,(17),[1,2,5,6,13,14],[146],150⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨150,[1,2,3,5,6,7,13,14,15],150⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid639 : RecordDataValid section14Catalog 5 (⟨25,(17),[1,5],[134],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_0608_0640 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 608).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 608).take 32 = [⟨25,(12),[1,2,5,6,13,14],[146],149⟩,⟨25,(12),[1,5],[134],84⟩,⟨25,(12),[5],[135],171⟩,⟨25,(12),[5,6],[131],171⟩,⟨25,(12),[5,6],[150],220⟩,⟨25,(13),[1,2,5,6],[130],84⟩,⟨25,(13),[1,2,5,6,13,14],[146],149⟩,⟨25,(13),[1,5],[134],84⟩,⟨25,(13),[5],[135],171⟩,⟨25,(13),[5,6],[131],171⟩,⟨25,(13),[5,6],[150],220⟩,⟨25,(14),[1,2,5,6],[130],83⟩,⟨25,(14),[1,2,5,6,13,14],[146],148⟩,⟨25,(14),[1,5],[134],83⟩,⟨25,(14),[5],[135],170⟩,⟨25,(14),[5,6],[131],170⟩,⟨25,(14),[5,6],[150],219⟩,⟨25,(15),[1,2,5,6],[130],35⟩,⟨25,(15),[1,2,5,6,13,14],[146],150⟩,⟨25,(15),[1,2,5,6,13,14],[150],196⟩,⟨25,(15),[1,5],[134],35⟩,⟨25,(15),[5],[135],172⟩,⟨25,(15),[5,6],[131],172⟩,⟨25,(16),[1,2,5,6],[130],35⟩,⟨25,(16),[1,2,5,6,13,14],[146],150⟩,⟨25,(16),[1,5],[134],35⟩,⟨25,(16),[5],[135],172⟩,⟨25,(16),[5,6],[131],172⟩,⟨25,(16),[5,6],[150],221⟩,⟨25,(17),[1,2,5,6],[130],35⟩,⟨25,(17),[1,2,5,6,13,14],[146],150⟩,⟨25,(17),[1,5],[134],35⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid608
  · exact recordValid_of_data section14Catalog 5 _ hnum valid609
  · exact recordValid_of_data section14Catalog 5 _ hnum valid610
  · exact recordValid_of_data section14Catalog 5 _ hnum valid611
  · exact recordValid_of_data section14Catalog 5 _ hnum valid612
  · exact recordValid_of_data section14Catalog 5 _ hnum valid613
  · exact recordValid_of_data section14Catalog 5 _ hnum valid614
  · exact recordValid_of_data section14Catalog 5 _ hnum valid615
  · exact recordValid_of_data section14Catalog 5 _ hnum valid616
  · exact recordValid_of_data section14Catalog 5 _ hnum valid617
  · exact recordValid_of_data section14Catalog 5 _ hnum valid618
  · exact recordValid_of_data section14Catalog 5 _ hnum valid619
  · exact recordValid_of_data section14Catalog 5 _ hnum valid620
  · exact recordValid_of_data section14Catalog 5 _ hnum valid621
  · exact recordValid_of_data section14Catalog 5 _ hnum valid622
  · exact recordValid_of_data section14Catalog 5 _ hnum valid623
  · exact recordValid_of_data section14Catalog 5 _ hnum valid624
  · exact recordValid_of_data section14Catalog 5 _ hnum valid625
  · exact recordValid_of_data section14Catalog 5 _ hnum valid626
  · exact recordValid_of_data section14Catalog 5 _ hnum valid627
  · exact recordValid_of_data section14Catalog 5 _ hnum valid628
  · exact recordValid_of_data section14Catalog 5 _ hnum valid629
  · exact recordValid_of_data section14Catalog 5 _ hnum valid630
  · exact recordValid_of_data section14Catalog 5 _ hnum valid631
  · exact recordValid_of_data section14Catalog 5 _ hnum valid632
  · exact recordValid_of_data section14Catalog 5 _ hnum valid633
  · exact recordValid_of_data section14Catalog 5 _ hnum valid634
  · exact recordValid_of_data section14Catalog 5 _ hnum valid635
  · exact recordValid_of_data section14Catalog 5 _ hnum valid636
  · exact recordValid_of_data section14Catalog 5 _ hnum valid637
  · exact recordValid_of_data section14Catalog 5 _ hnum valid638
  · exact recordValid_of_data section14Catalog 5 _ hnum valid639
end Section14Records_5_608_640

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_0608_0640

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 512).take 128, section14RecordValid section14Catalog 5 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (5 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 5 r
  exact (all_of_interval_split P xs 512 576 640 (by decide) (by decide) (all_of_interval_split P xs 512 544 576 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_0512_0544 hnum) (Freiman.workReverse20260919_s0005_records_0544_0576 hnum)) (all_of_interval_split P xs 576 608 640 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_0576_0608 hnum) (Freiman.workReverse20260919_s0005_records_0608_0640 hnum)))

#print axioms solution
