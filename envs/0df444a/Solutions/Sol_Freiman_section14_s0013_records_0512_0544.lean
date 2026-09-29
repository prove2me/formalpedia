-- Prove2me | solution 1 for Freiman.section14_s0013_records_0512_0544
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T11:51:12.102747+00:00
-- url     : https://prove2.me/submissions/2bf4550d-91ea-4468-9367-cede30eda28b

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
namespace Section14Records_13_512_544
private theorem valid512 : RecordDataValid section14Catalog 13 (⟨23,(14),[1,13],[151],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid513 : RecordDataValid section14Catalog 13 (⟨23,(15),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid514 : RecordDataValid section14Catalog 13 (⟨23,(15),[1,2,13,14],[147,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid515 : RecordDataValid section14Catalog 13 (⟨23,(15),[1,5,13],[135],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid516 : RecordDataValid section14Catalog 13 (⟨23,(15),[1,13],[151],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid517 : RecordDataValid section14Catalog 13 (⟨23,(16),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid518 : RecordDataValid section14Catalog 13 (⟨23,(16),[1,2,13,14],[147,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid519 : RecordDataValid section14Catalog 13 (⟨23,(16),[1,5,13],[135],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid520 : RecordDataValid section14Catalog 13 (⟨23,(16),[1,13],[151],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid521 : RecordDataValid section14Catalog 13 (⟨23,(17),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid522 : RecordDataValid section14Catalog 13 (⟨23,(17),[1,2,13,14],[147,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid523 : RecordDataValid section14Catalog 13 (⟨23,(17),[1,5,13],[135],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid524 : RecordDataValid section14Catalog 13 (⟨23,(17),[1,13],[151],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid525 : RecordDataValid section14Catalog 13 (⟨23,(18),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid526 : RecordDataValid section14Catalog 13 (⟨23,(18),[1,2,13,14],[147,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid527 : RecordDataValid section14Catalog 13 (⟨23,(18),[1,5,13],[135],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid528 : RecordDataValid section14Catalog 13 (⟨23,(18),[1,13],[151],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid529 : RecordDataValid section14Catalog 13 (⟨23,(19),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid530 : RecordDataValid section14Catalog 13 (⟨23,(19),[1,2,13,14],[147,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid531 : RecordDataValid section14Catalog 13 (⟨23,(19),[1,5,13],[135],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid532 : RecordDataValid section14Catalog 13 (⟨23,(19),[1,13],[151],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid533 : RecordDataValid section14Catalog 13 (⟨23,(20),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid534 : RecordDataValid section14Catalog 13 (⟨23,(20),[1,2,13,14],[147,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid535 : RecordDataValid section14Catalog 13 (⟨23,(20),[1,5,13],[135],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid536 : RecordDataValid section14Catalog 13 (⟨23,(20),[1,13],[151],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid537 : RecordDataValid section14Catalog 13 (⟨23,(21),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid538 : RecordDataValid section14Catalog 13 (⟨23,(21),[1,2,13,14],[147,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid539 : RecordDataValid section14Catalog 13 (⟨23,(21),[1,5,13],[135],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid540 : RecordDataValid section14Catalog 13 (⟨23,(21),[1,13],[151],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid541 : RecordDataValid section14Catalog 13 (⟨23,(22),[1,2,5,6,13,14],[131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid542 : RecordDataValid section14Catalog 13 (⟨23,(22),[1,2,13,14],[147,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid543 : RecordDataValid section14Catalog 13 (⟨23,(22),[1,5,13],[135],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 512).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 512).take 32 = [⟨23,(14),[1,13],[151],2⟩,⟨23,(15),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(15),[1,2,13,14],[147,190],2⟩,⟨23,(15),[1,5,13],[135],2⟩,⟨23,(15),[1,13],[151],2⟩,⟨23,(16),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(16),[1,2,13,14],[147,190],2⟩,⟨23,(16),[1,5,13],[135],2⟩,⟨23,(16),[1,13],[151],2⟩,⟨23,(17),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(17),[1,2,13,14],[147,190],2⟩,⟨23,(17),[1,5,13],[135],2⟩,⟨23,(17),[1,13],[151],2⟩,⟨23,(18),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(18),[1,2,13,14],[147,190],2⟩,⟨23,(18),[1,5,13],[135],2⟩,⟨23,(18),[1,13],[151],2⟩,⟨23,(19),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(19),[1,2,13,14],[147,190],2⟩,⟨23,(19),[1,5,13],[135],2⟩,⟨23,(19),[1,13],[151],2⟩,⟨23,(20),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(20),[1,2,13,14],[147,190],2⟩,⟨23,(20),[1,5,13],[135],2⟩,⟨23,(20),[1,13],[151],2⟩,⟨23,(21),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(21),[1,2,13,14],[147,190],2⟩,⟨23,(21),[1,5,13],[135],2⟩,⟨23,(21),[1,13],[151],2⟩,⟨23,(22),[1,2,5,6,13,14],[131,146,150],2⟩,⟨23,(22),[1,2,13,14],[147,190],2⟩,⟨23,(22),[1,5,13],[135],2⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid512
  · exact recordValid_of_data section14Catalog 13 _ hnum valid513
  · exact recordValid_of_data section14Catalog 13 _ hnum valid514
  · exact recordValid_of_data section14Catalog 13 _ hnum valid515
  · exact recordValid_of_data section14Catalog 13 _ hnum valid516
  · exact recordValid_of_data section14Catalog 13 _ hnum valid517
  · exact recordValid_of_data section14Catalog 13 _ hnum valid518
  · exact recordValid_of_data section14Catalog 13 _ hnum valid519
  · exact recordValid_of_data section14Catalog 13 _ hnum valid520
  · exact recordValid_of_data section14Catalog 13 _ hnum valid521
  · exact recordValid_of_data section14Catalog 13 _ hnum valid522
  · exact recordValid_of_data section14Catalog 13 _ hnum valid523
  · exact recordValid_of_data section14Catalog 13 _ hnum valid524
  · exact recordValid_of_data section14Catalog 13 _ hnum valid525
  · exact recordValid_of_data section14Catalog 13 _ hnum valid526
  · exact recordValid_of_data section14Catalog 13 _ hnum valid527
  · exact recordValid_of_data section14Catalog 13 _ hnum valid528
  · exact recordValid_of_data section14Catalog 13 _ hnum valid529
  · exact recordValid_of_data section14Catalog 13 _ hnum valid530
  · exact recordValid_of_data section14Catalog 13 _ hnum valid531
  · exact recordValid_of_data section14Catalog 13 _ hnum valid532
  · exact recordValid_of_data section14Catalog 13 _ hnum valid533
  · exact recordValid_of_data section14Catalog 13 _ hnum valid534
  · exact recordValid_of_data section14Catalog 13 _ hnum valid535
  · exact recordValid_of_data section14Catalog 13 _ hnum valid536
  · exact recordValid_of_data section14Catalog 13 _ hnum valid537
  · exact recordValid_of_data section14Catalog 13 _ hnum valid538
  · exact recordValid_of_data section14Catalog 13 _ hnum valid539
  · exact recordValid_of_data section14Catalog 13 _ hnum valid540
  · exact recordValid_of_data section14Catalog 13 _ hnum valid541
  · exact recordValid_of_data section14Catalog 13 _ hnum valid542
  · exact recordValid_of_data section14Catalog 13 _ hnum valid543
end Section14Records_13_512_544

#print axioms solution
