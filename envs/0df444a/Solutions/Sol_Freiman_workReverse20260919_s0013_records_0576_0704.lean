-- Prove2me | solution 1 for Freiman.workReverse20260919_s0013_records_0576_0704
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:50:01.373252+00:00
-- url     : https://prove2.me/submissions/69f5ef34-e328-4088-bb93-32ba86787c46

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_0576_0608
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_576_608
private theorem valid576 : RecordDataValid section14Catalog 13 (⟨25,(3),[1,2,13,14],[147],169⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨169,[1,2,5,6,9,10,13,14],169⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid577 : RecordDataValid section14Catalog 13 (⟨25,(3),[1,2,13,14],[150],192⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨192,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],192⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid578 : RecordDataValid section14Catalog 13 (⟨25,(3),[1,2,13,14],[190],218⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨218,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],218⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid579 : RecordDataValid section14Catalog 13 (⟨25,(3),[1,13],[135],82⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨82,[1,2,5,6,9,10,12,13,14],82⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid580 : RecordDataValid section14Catalog 13 (⟨25,(3),[1,13],[151],169⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨169,[1,2,5,6,9,10,13,14],169⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid581 : RecordDataValid section14Catalog 13 (⟨25,(4),[1,2,5,6,13,14],[146],148⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨148,[1,2,3,5,6,7,13,14,15],148⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid582 : RecordDataValid section14Catalog 13 (⟨25,(4),[1,2,13,14],[131],83⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨83,[1,2,5,6,9,10,12,13,14],83⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid583 : RecordDataValid section14Catalog 13 (⟨25,(4),[1,2,13,14],[147],170⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨170,[1,2,5,6,9,10,13,14],170⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid584 : RecordDataValid section14Catalog 13 (⟨25,(4),[1,2,13,14],[150],193⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨193,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],193⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid585 : RecordDataValid section14Catalog 13 (⟨25,(4),[1,2,13,14],[190],219⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨219,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],219⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid586 : RecordDataValid section14Catalog 13 (⟨25,(4),[1,13],[135],83⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨83,[1,2,5,6,9,10,12,13,14],83⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid587 : RecordDataValid section14Catalog 13 (⟨25,(4),[1,13],[151],170⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨170,[1,2,5,6,9,10,13,14],170⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid588 : RecordDataValid section14Catalog 13 (⟨25,(5),[1,2,5,6,13,14],[146],145⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨145,[1,2,3,5,6,7,13,14,15],145⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid589 : RecordDataValid section14Catalog 13 (⟨25,(5),[1,2,5,6,13,14],[150],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid590 : RecordDataValid section14Catalog 13 (⟨25,(5),[1,2,13,14],[131],80⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨80,[1,2,5,6,9,10,12,13,14],80⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid591 : RecordDataValid section14Catalog 13 (⟨25,(5),[1,2,13,14],[147],167⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨167,[1,2,5,6,9,10,13,14],167⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid592 : RecordDataValid section14Catalog 13 (⟨25,(5),[1,2,13,14],[190],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid593 : RecordDataValid section14Catalog 13 (⟨25,(5),[1,13],[135],80⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨80,[1,2,5,6,9,10,12,13,14],80⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid594 : RecordDataValid section14Catalog 13 (⟨25,(5),[1,13],[151],167⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨167,[1,2,5,6,9,10,13,14],167⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid595 : RecordDataValid section14Catalog 13 (⟨25,(6),[1,2,5,6,13,14],[146],146⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨146,[1,2,3,5,6,7,13,14,15],146⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid596 : RecordDataValid section14Catalog 13 (⟨25,(6),[1,2,13,14],[131],81⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨81,[1,2,5,6,9,10,12,13,14],81⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid597 : RecordDataValid section14Catalog 13 (⟨25,(6),[1,2,13,14],[147],168⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨168,[1,2,5,6,9,10,13,14],168⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid598 : RecordDataValid section14Catalog 13 (⟨25,(6),[1,2,13,14],[150],190⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨190,[1,2,3,4,5,6,7,13,14,15,16],190⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid599 : RecordDataValid section14Catalog 13 (⟨25,(6),[1,2,13,14],[190],216⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨216,[1,2,3,5,6,7,8,9,10,11,12,13,14,15],216⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid600 : RecordDataValid section14Catalog 13 (⟨25,(6),[1,13],[135],81⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨81,[1,2,5,6,9,10,12,13,14],81⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid601 : RecordDataValid section14Catalog 13 (⟨25,(6),[1,13],[151],168⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨168,[1,2,5,6,9,10,13,14],168⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid602 : RecordDataValid section14Catalog 13 (⟨25,(7),[1,2,5,6,13,14],[146],145⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨145,[1,2,3,5,6,7,13,14,15],145⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid603 : RecordDataValid section14Catalog 13 (⟨25,(7),[1,2,13,14],[131],80⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨80,[1,2,5,6,9,10,12,13,14],80⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid604 : RecordDataValid section14Catalog 13 (⟨25,(7),[1,2,13,14],[147],167⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨167,[1,2,5,6,9,10,13,14],167⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid605 : RecordDataValid section14Catalog 13 (⟨25,(7),[1,2,13,14],[150],191⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨191,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],191⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid606 : RecordDataValid section14Catalog 13 (⟨25,(7),[1,2,13,14],[190],217⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨217,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],217⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid607 : RecordDataValid section14Catalog 13 (⟨25,(7),[1,13],[135],80⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨80,[1,2,5,6,9,10,12,13,14],80⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_0576_0608 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 576).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 576).take 32 = [⟨25,(3),[1,2,13,14],[147],169⟩,⟨25,(3),[1,2,13,14],[150],192⟩,⟨25,(3),[1,2,13,14],[190],218⟩,⟨25,(3),[1,13],[135],82⟩,⟨25,(3),[1,13],[151],169⟩,⟨25,(4),[1,2,5,6,13,14],[146],148⟩,⟨25,(4),[1,2,13,14],[131],83⟩,⟨25,(4),[1,2,13,14],[147],170⟩,⟨25,(4),[1,2,13,14],[150],193⟩,⟨25,(4),[1,2,13,14],[190],219⟩,⟨25,(4),[1,13],[135],83⟩,⟨25,(4),[1,13],[151],170⟩,⟨25,(5),[1,2,5,6,13,14],[146],145⟩,⟨25,(5),[1,2,5,6,13,14],[150],189⟩,⟨25,(5),[1,2,13,14],[131],80⟩,⟨25,(5),[1,2,13,14],[147],167⟩,⟨25,(5),[1,2,13,14],[190],189⟩,⟨25,(5),[1,13],[135],80⟩,⟨25,(5),[1,13],[151],167⟩,⟨25,(6),[1,2,5,6,13,14],[146],146⟩,⟨25,(6),[1,2,13,14],[131],81⟩,⟨25,(6),[1,2,13,14],[147],168⟩,⟨25,(6),[1,2,13,14],[150],190⟩,⟨25,(6),[1,2,13,14],[190],216⟩,⟨25,(6),[1,13],[135],81⟩,⟨25,(6),[1,13],[151],168⟩,⟨25,(7),[1,2,5,6,13,14],[146],145⟩,⟨25,(7),[1,2,13,14],[131],80⟩,⟨25,(7),[1,2,13,14],[147],167⟩,⟨25,(7),[1,2,13,14],[150],191⟩,⟨25,(7),[1,2,13,14],[190],217⟩,⟨25,(7),[1,13],[135],80⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid576
  · exact recordValid_of_data section14Catalog 13 _ hnum valid577
  · exact recordValid_of_data section14Catalog 13 _ hnum valid578
  · exact recordValid_of_data section14Catalog 13 _ hnum valid579
  · exact recordValid_of_data section14Catalog 13 _ hnum valid580
  · exact recordValid_of_data section14Catalog 13 _ hnum valid581
  · exact recordValid_of_data section14Catalog 13 _ hnum valid582
  · exact recordValid_of_data section14Catalog 13 _ hnum valid583
  · exact recordValid_of_data section14Catalog 13 _ hnum valid584
  · exact recordValid_of_data section14Catalog 13 _ hnum valid585
  · exact recordValid_of_data section14Catalog 13 _ hnum valid586
  · exact recordValid_of_data section14Catalog 13 _ hnum valid587
  · exact recordValid_of_data section14Catalog 13 _ hnum valid588
  · exact recordValid_of_data section14Catalog 13 _ hnum valid589
  · exact recordValid_of_data section14Catalog 13 _ hnum valid590
  · exact recordValid_of_data section14Catalog 13 _ hnum valid591
  · exact recordValid_of_data section14Catalog 13 _ hnum valid592
  · exact recordValid_of_data section14Catalog 13 _ hnum valid593
  · exact recordValid_of_data section14Catalog 13 _ hnum valid594
  · exact recordValid_of_data section14Catalog 13 _ hnum valid595
  · exact recordValid_of_data section14Catalog 13 _ hnum valid596
  · exact recordValid_of_data section14Catalog 13 _ hnum valid597
  · exact recordValid_of_data section14Catalog 13 _ hnum valid598
  · exact recordValid_of_data section14Catalog 13 _ hnum valid599
  · exact recordValid_of_data section14Catalog 13 _ hnum valid600
  · exact recordValid_of_data section14Catalog 13 _ hnum valid601
  · exact recordValid_of_data section14Catalog 13 _ hnum valid602
  · exact recordValid_of_data section14Catalog 13 _ hnum valid603
  · exact recordValid_of_data section14Catalog 13 _ hnum valid604
  · exact recordValid_of_data section14Catalog 13 _ hnum valid605
  · exact recordValid_of_data section14Catalog 13 _ hnum valid606
  · exact recordValid_of_data section14Catalog 13 _ hnum valid607
end Section14Records_13_576_608

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_0576_0608


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_0608_0640
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_608_640
private theorem valid608 : RecordDataValid section14Catalog 13 (⟨25,(7),[1,13],[151],167⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨167,[1,2,5,6,9,10,13,14],167⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid609 : RecordDataValid section14Catalog 13 (⟨25,(8),[1,2,5,6,13,14],[146],147⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨147,[1,2,3,5,6,7,13,14,15],147⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid610 : RecordDataValid section14Catalog 13 (⟨25,(8),[1,2,13,14],[131],82⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨82,[1,2,5,6,9,10,12,13,14],82⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid611 : RecordDataValid section14Catalog 13 (⟨25,(8),[1,2,13,14],[147],169⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨169,[1,2,5,6,9,10,13,14],169⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid612 : RecordDataValid section14Catalog 13 (⟨25,(8),[1,2,13,14],[150],192⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨192,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],192⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid613 : RecordDataValid section14Catalog 13 (⟨25,(8),[1,2,13,14],[190],218⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨218,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],218⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid614 : RecordDataValid section14Catalog 13 (⟨25,(8),[1,13],[135],82⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨82,[1,2,5,6,9,10,12,13,14],82⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid615 : RecordDataValid section14Catalog 13 (⟨25,(8),[1,13],[151],169⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨169,[1,2,5,6,9,10,13,14],169⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid616 : RecordDataValid section14Catalog 13 (⟨25,(9),[1,2,5,6,13,14],[146],148⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨148,[1,2,3,5,6,7,13,14,15],148⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid617 : RecordDataValid section14Catalog 13 (⟨25,(9),[1,2,13,14],[131],83⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨83,[1,2,5,6,9,10,12,13,14],83⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid618 : RecordDataValid section14Catalog 13 (⟨25,(9),[1,2,13,14],[147],170⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨170,[1,2,5,6,9,10,13,14],170⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid619 : RecordDataValid section14Catalog 13 (⟨25,(9),[1,2,13,14],[150],193⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨193,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],193⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid620 : RecordDataValid section14Catalog 13 (⟨25,(9),[1,2,13,14],[190],219⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨219,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],219⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid621 : RecordDataValid section14Catalog 13 (⟨25,(9),[1,13],[135],83⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨83,[1,2,5,6,9,10,12,13,14],83⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid622 : RecordDataValid section14Catalog 13 (⟨25,(9),[1,13],[151],170⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨170,[1,2,5,6,9,10,13,14],170⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid623 : RecordDataValid section14Catalog 13 (⟨25,(10),[1,2,5,6,13,14],[146],149⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨149,[1,2,3,5,6,7,13,14,15],149⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid624 : RecordDataValid section14Catalog 13 (⟨25,(10),[1,2,5,6,13,14],[150],194⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨194,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],194⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid625 : RecordDataValid section14Catalog 13 (⟨25,(10),[1,2,13,14],[131],84⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid626 : RecordDataValid section14Catalog 13 (⟨25,(10),[1,2,13,14],[147],171⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨171,[1,2,5,6,9,10,13,14],171⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid627 : RecordDataValid section14Catalog 13 (⟨25,(10),[1,2,13,14],[190],194⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨194,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],194⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid628 : RecordDataValid section14Catalog 13 (⟨25,(10),[1,13],[135],84⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid629 : RecordDataValid section14Catalog 13 (⟨25,(10),[1,13],[151],171⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨171,[1,2,5,6,9,10,13,14],171⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid630 : RecordDataValid section14Catalog 13 (⟨25,(11),[1,2,5,6,13,14],[146],149⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨149,[1,2,3,5,6,7,13,14,15],149⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid631 : RecordDataValid section14Catalog 13 (⟨25,(11),[1,2,13,14],[131],84⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid632 : RecordDataValid section14Catalog 13 (⟨25,(11),[1,2,13,14],[147],171⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨171,[1,2,5,6,9,10,13,14],171⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid633 : RecordDataValid section14Catalog 13 (⟨25,(11),[1,2,13,14],[150],195⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨195,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],195⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid634 : RecordDataValid section14Catalog 13 (⟨25,(11),[1,2,13,14],[190],220⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨220,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],220⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid635 : RecordDataValid section14Catalog 13 (⟨25,(11),[1,13],[135],84⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid636 : RecordDataValid section14Catalog 13 (⟨25,(11),[1,13],[151],171⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨171,[1,2,5,6,9,10,13,14],171⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid637 : RecordDataValid section14Catalog 13 (⟨25,(12),[1,2,5,6,13,14],[146],149⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨149,[1,2,3,5,6,7,13,14,15],149⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid638 : RecordDataValid section14Catalog 13 (⟨25,(12),[1,2,13,14],[131],84⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid639 : RecordDataValid section14Catalog 13 (⟨25,(12),[1,2,13,14],[147],171⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨171,[1,2,5,6,9,10,13,14],171⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_0608_0640 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 608).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 608).take 32 = [⟨25,(7),[1,13],[151],167⟩,⟨25,(8),[1,2,5,6,13,14],[146],147⟩,⟨25,(8),[1,2,13,14],[131],82⟩,⟨25,(8),[1,2,13,14],[147],169⟩,⟨25,(8),[1,2,13,14],[150],192⟩,⟨25,(8),[1,2,13,14],[190],218⟩,⟨25,(8),[1,13],[135],82⟩,⟨25,(8),[1,13],[151],169⟩,⟨25,(9),[1,2,5,6,13,14],[146],148⟩,⟨25,(9),[1,2,13,14],[131],83⟩,⟨25,(9),[1,2,13,14],[147],170⟩,⟨25,(9),[1,2,13,14],[150],193⟩,⟨25,(9),[1,2,13,14],[190],219⟩,⟨25,(9),[1,13],[135],83⟩,⟨25,(9),[1,13],[151],170⟩,⟨25,(10),[1,2,5,6,13,14],[146],149⟩,⟨25,(10),[1,2,5,6,13,14],[150],194⟩,⟨25,(10),[1,2,13,14],[131],84⟩,⟨25,(10),[1,2,13,14],[147],171⟩,⟨25,(10),[1,2,13,14],[190],194⟩,⟨25,(10),[1,13],[135],84⟩,⟨25,(10),[1,13],[151],171⟩,⟨25,(11),[1,2,5,6,13,14],[146],149⟩,⟨25,(11),[1,2,13,14],[131],84⟩,⟨25,(11),[1,2,13,14],[147],171⟩,⟨25,(11),[1,2,13,14],[150],195⟩,⟨25,(11),[1,2,13,14],[190],220⟩,⟨25,(11),[1,13],[135],84⟩,⟨25,(11),[1,13],[151],171⟩,⟨25,(12),[1,2,5,6,13,14],[146],149⟩,⟨25,(12),[1,2,13,14],[131],84⟩,⟨25,(12),[1,2,13,14],[147],171⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid608
  · exact recordValid_of_data section14Catalog 13 _ hnum valid609
  · exact recordValid_of_data section14Catalog 13 _ hnum valid610
  · exact recordValid_of_data section14Catalog 13 _ hnum valid611
  · exact recordValid_of_data section14Catalog 13 _ hnum valid612
  · exact recordValid_of_data section14Catalog 13 _ hnum valid613
  · exact recordValid_of_data section14Catalog 13 _ hnum valid614
  · exact recordValid_of_data section14Catalog 13 _ hnum valid615
  · exact recordValid_of_data section14Catalog 13 _ hnum valid616
  · exact recordValid_of_data section14Catalog 13 _ hnum valid617
  · exact recordValid_of_data section14Catalog 13 _ hnum valid618
  · exact recordValid_of_data section14Catalog 13 _ hnum valid619
  · exact recordValid_of_data section14Catalog 13 _ hnum valid620
  · exact recordValid_of_data section14Catalog 13 _ hnum valid621
  · exact recordValid_of_data section14Catalog 13 _ hnum valid622
  · exact recordValid_of_data section14Catalog 13 _ hnum valid623
  · exact recordValid_of_data section14Catalog 13 _ hnum valid624
  · exact recordValid_of_data section14Catalog 13 _ hnum valid625
  · exact recordValid_of_data section14Catalog 13 _ hnum valid626
  · exact recordValid_of_data section14Catalog 13 _ hnum valid627
  · exact recordValid_of_data section14Catalog 13 _ hnum valid628
  · exact recordValid_of_data section14Catalog 13 _ hnum valid629
  · exact recordValid_of_data section14Catalog 13 _ hnum valid630
  · exact recordValid_of_data section14Catalog 13 _ hnum valid631
  · exact recordValid_of_data section14Catalog 13 _ hnum valid632
  · exact recordValid_of_data section14Catalog 13 _ hnum valid633
  · exact recordValid_of_data section14Catalog 13 _ hnum valid634
  · exact recordValid_of_data section14Catalog 13 _ hnum valid635
  · exact recordValid_of_data section14Catalog 13 _ hnum valid636
  · exact recordValid_of_data section14Catalog 13 _ hnum valid637
  · exact recordValid_of_data section14Catalog 13 _ hnum valid638
  · exact recordValid_of_data section14Catalog 13 _ hnum valid639
end Section14Records_13_608_640

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_0608_0640


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_0640_0672
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_640_672
private theorem valid640 : RecordDataValid section14Catalog 13 (⟨25,(12),[1,2,13,14],[150],195⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨195,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],195⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid641 : RecordDataValid section14Catalog 13 (⟨25,(12),[1,2,13,14],[190],220⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨220,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],220⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid642 : RecordDataValid section14Catalog 13 (⟨25,(12),[1,13],[135],84⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid643 : RecordDataValid section14Catalog 13 (⟨25,(12),[1,13],[151],171⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨171,[1,2,5,6,9,10,13,14],171⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid644 : RecordDataValid section14Catalog 13 (⟨25,(13),[1,2,5,6,13,14],[146],149⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨149,[1,2,3,5,6,7,13,14,15],149⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid645 : RecordDataValid section14Catalog 13 (⟨25,(13),[1,2,13,14],[131],84⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid646 : RecordDataValid section14Catalog 13 (⟨25,(13),[1,2,13,14],[147],171⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨171,[1,2,5,6,9,10,13,14],171⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid647 : RecordDataValid section14Catalog 13 (⟨25,(13),[1,2,13,14],[150],195⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨195,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],195⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid648 : RecordDataValid section14Catalog 13 (⟨25,(13),[1,2,13,14],[190],220⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨220,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],220⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid649 : RecordDataValid section14Catalog 13 (⟨25,(13),[1,13],[135],84⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid650 : RecordDataValid section14Catalog 13 (⟨25,(13),[1,13],[151],171⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨171,[1,2,5,6,9,10,13,14],171⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid651 : RecordDataValid section14Catalog 13 (⟨25,(14),[1,2,5,6,13,14],[146],148⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨148,[1,2,3,5,6,7,13,14,15],148⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid652 : RecordDataValid section14Catalog 13 (⟨25,(14),[1,2,13,14],[131],83⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨83,[1,2,5,6,9,10,12,13,14],83⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid653 : RecordDataValid section14Catalog 13 (⟨25,(14),[1,2,13,14],[147],170⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨170,[1,2,5,6,9,10,13,14],170⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid654 : RecordDataValid section14Catalog 13 (⟨25,(14),[1,2,13,14],[150],193⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨193,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],193⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid655 : RecordDataValid section14Catalog 13 (⟨25,(14),[1,2,13,14],[190],219⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨219,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],219⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid656 : RecordDataValid section14Catalog 13 (⟨25,(14),[1,13],[135],83⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨83,[1,2,5,6,9,10,12,13,14],83⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid657 : RecordDataValid section14Catalog 13 (⟨25,(14),[1,13],[151],170⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨170,[1,2,5,6,9,10,13,14],170⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid658 : RecordDataValid section14Catalog 13 (⟨25,(15),[1,2,5,6,13,14],[146],150⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨150,[1,2,3,5,6,7,13,14,15],150⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid659 : RecordDataValid section14Catalog 13 (⟨25,(15),[1,2,5,6,13,14],[150],196⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨196,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],196⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid660 : RecordDataValid section14Catalog 13 (⟨25,(15),[1,2,13,14],[131],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid661 : RecordDataValid section14Catalog 13 (⟨25,(15),[1,2,13,14],[147],172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨172,[1,2,5,6,9,10,13,14],172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid662 : RecordDataValid section14Catalog 13 (⟨25,(15),[1,2,13,14],[190],196⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨196,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],196⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid663 : RecordDataValid section14Catalog 13 (⟨25,(15),[1,13],[135],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid664 : RecordDataValid section14Catalog 13 (⟨25,(15),[1,13],[151],172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨172,[1,2,5,6,9,10,13,14],172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid665 : RecordDataValid section14Catalog 13 (⟨25,(16),[1,2,5,6,13,14],[146],150⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨150,[1,2,3,5,6,7,13,14,15],150⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid666 : RecordDataValid section14Catalog 13 (⟨25,(16),[1,2,13,14],[131],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid667 : RecordDataValid section14Catalog 13 (⟨25,(16),[1,2,13,14],[147],172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨172,[1,2,5,6,9,10,13,14],172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid668 : RecordDataValid section14Catalog 13 (⟨25,(16),[1,2,13,14],[150],197⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨197,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],197⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid669 : RecordDataValid section14Catalog 13 (⟨25,(16),[1,2,13,14],[190],221⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨221,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],221⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid670 : RecordDataValid section14Catalog 13 (⟨25,(16),[1,13],[135],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid671 : RecordDataValid section14Catalog 13 (⟨25,(16),[1,13],[151],172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨172,[1,2,5,6,9,10,13,14],172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_0640_0672 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 640).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 640).take 32 = [⟨25,(12),[1,2,13,14],[150],195⟩,⟨25,(12),[1,2,13,14],[190],220⟩,⟨25,(12),[1,13],[135],84⟩,⟨25,(12),[1,13],[151],171⟩,⟨25,(13),[1,2,5,6,13,14],[146],149⟩,⟨25,(13),[1,2,13,14],[131],84⟩,⟨25,(13),[1,2,13,14],[147],171⟩,⟨25,(13),[1,2,13,14],[150],195⟩,⟨25,(13),[1,2,13,14],[190],220⟩,⟨25,(13),[1,13],[135],84⟩,⟨25,(13),[1,13],[151],171⟩,⟨25,(14),[1,2,5,6,13,14],[146],148⟩,⟨25,(14),[1,2,13,14],[131],83⟩,⟨25,(14),[1,2,13,14],[147],170⟩,⟨25,(14),[1,2,13,14],[150],193⟩,⟨25,(14),[1,2,13,14],[190],219⟩,⟨25,(14),[1,13],[135],83⟩,⟨25,(14),[1,13],[151],170⟩,⟨25,(15),[1,2,5,6,13,14],[146],150⟩,⟨25,(15),[1,2,5,6,13,14],[150],196⟩,⟨25,(15),[1,2,13,14],[131],35⟩,⟨25,(15),[1,2,13,14],[147],172⟩,⟨25,(15),[1,2,13,14],[190],196⟩,⟨25,(15),[1,13],[135],35⟩,⟨25,(15),[1,13],[151],172⟩,⟨25,(16),[1,2,5,6,13,14],[146],150⟩,⟨25,(16),[1,2,13,14],[131],35⟩,⟨25,(16),[1,2,13,14],[147],172⟩,⟨25,(16),[1,2,13,14],[150],197⟩,⟨25,(16),[1,2,13,14],[190],221⟩,⟨25,(16),[1,13],[135],35⟩,⟨25,(16),[1,13],[151],172⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid640
  · exact recordValid_of_data section14Catalog 13 _ hnum valid641
  · exact recordValid_of_data section14Catalog 13 _ hnum valid642
  · exact recordValid_of_data section14Catalog 13 _ hnum valid643
  · exact recordValid_of_data section14Catalog 13 _ hnum valid644
  · exact recordValid_of_data section14Catalog 13 _ hnum valid645
  · exact recordValid_of_data section14Catalog 13 _ hnum valid646
  · exact recordValid_of_data section14Catalog 13 _ hnum valid647
  · exact recordValid_of_data section14Catalog 13 _ hnum valid648
  · exact recordValid_of_data section14Catalog 13 _ hnum valid649
  · exact recordValid_of_data section14Catalog 13 _ hnum valid650
  · exact recordValid_of_data section14Catalog 13 _ hnum valid651
  · exact recordValid_of_data section14Catalog 13 _ hnum valid652
  · exact recordValid_of_data section14Catalog 13 _ hnum valid653
  · exact recordValid_of_data section14Catalog 13 _ hnum valid654
  · exact recordValid_of_data section14Catalog 13 _ hnum valid655
  · exact recordValid_of_data section14Catalog 13 _ hnum valid656
  · exact recordValid_of_data section14Catalog 13 _ hnum valid657
  · exact recordValid_of_data section14Catalog 13 _ hnum valid658
  · exact recordValid_of_data section14Catalog 13 _ hnum valid659
  · exact recordValid_of_data section14Catalog 13 _ hnum valid660
  · exact recordValid_of_data section14Catalog 13 _ hnum valid661
  · exact recordValid_of_data section14Catalog 13 _ hnum valid662
  · exact recordValid_of_data section14Catalog 13 _ hnum valid663
  · exact recordValid_of_data section14Catalog 13 _ hnum valid664
  · exact recordValid_of_data section14Catalog 13 _ hnum valid665
  · exact recordValid_of_data section14Catalog 13 _ hnum valid666
  · exact recordValid_of_data section14Catalog 13 _ hnum valid667
  · exact recordValid_of_data section14Catalog 13 _ hnum valid668
  · exact recordValid_of_data section14Catalog 13 _ hnum valid669
  · exact recordValid_of_data section14Catalog 13 _ hnum valid670
  · exact recordValid_of_data section14Catalog 13 _ hnum valid671
end Section14Records_13_640_672

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_0640_0672


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_0672_0704
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_672_704
private theorem valid672 : RecordDataValid section14Catalog 13 (⟨25,(17),[1,2,5,6,13,14],[146],150⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨150,[1,2,3,5,6,7,13,14,15],150⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid673 : RecordDataValid section14Catalog 13 (⟨25,(17),[1,2,13,14],[131],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid674 : RecordDataValid section14Catalog 13 (⟨25,(17),[1,2,13,14],[147],172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨172,[1,2,5,6,9,10,13,14],172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid675 : RecordDataValid section14Catalog 13 (⟨25,(17),[1,2,13,14],[150],197⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨197,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],197⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid676 : RecordDataValid section14Catalog 13 (⟨25,(17),[1,2,13,14],[190],221⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨221,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],221⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid677 : RecordDataValid section14Catalog 13 (⟨25,(17),[1,13],[135],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid678 : RecordDataValid section14Catalog 13 (⟨25,(17),[1,13],[151],172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨172,[1,2,5,6,9,10,13,14],172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid679 : RecordDataValid section14Catalog 13 (⟨25,(18),[1,2,5,6,13,14],[146],150⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨150,[1,2,3,5,6,7,13,14,15],150⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid680 : RecordDataValid section14Catalog 13 (⟨25,(18),[1,2,13,14],[131],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid681 : RecordDataValid section14Catalog 13 (⟨25,(18),[1,2,13,14],[147],172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨172,[1,2,5,6,9,10,13,14],172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid682 : RecordDataValid section14Catalog 13 (⟨25,(18),[1,2,13,14],[150],197⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨197,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],197⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid683 : RecordDataValid section14Catalog 13 (⟨25,(18),[1,2,13,14],[190],221⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨221,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],221⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid684 : RecordDataValid section14Catalog 13 (⟨25,(18),[1,13],[135],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid685 : RecordDataValid section14Catalog 13 (⟨25,(18),[1,13],[151],172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨172,[1,2,5,6,9,10,13,14],172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid686 : RecordDataValid section14Catalog 13 (⟨25,(19),[1,2,5,6,13,14],[146],150⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨150,[1,2,3,5,6,7,13,14,15],150⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid687 : RecordDataValid section14Catalog 13 (⟨25,(19),[1,2,13,14],[131],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid688 : RecordDataValid section14Catalog 13 (⟨25,(19),[1,2,13,14],[147],172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨172,[1,2,5,6,9,10,13,14],172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid689 : RecordDataValid section14Catalog 13 (⟨25,(19),[1,2,13,14],[150],197⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨197,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],197⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid690 : RecordDataValid section14Catalog 13 (⟨25,(19),[1,2,13,14],[190],221⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨221,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],221⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid691 : RecordDataValid section14Catalog 13 (⟨25,(19),[1,13],[135],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid692 : RecordDataValid section14Catalog 13 (⟨25,(19),[1,13],[151],172⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨172,[1,2,5,6,9,10,13,14],172⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid693 : RecordDataValid section14Catalog 13 (⟨25,(20),[1,2,5,6,13,14],[146],151⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨151,[1,2,3,5,6,7,13,14,15],151⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid694 : RecordDataValid section14Catalog 13 (⟨25,(20),[1,2,5,6,13,14],[150],198⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨198,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],198⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid695 : RecordDataValid section14Catalog 13 (⟨25,(20),[1,2,13,14],[131],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid696 : RecordDataValid section14Catalog 13 (⟨25,(20),[1,2,13,14],[147],173⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨173,[1,2,5,6,9,10,13,14],173⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid697 : RecordDataValid section14Catalog 13 (⟨25,(20),[1,2,13,14],[190],198⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨198,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],198⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid698 : RecordDataValid section14Catalog 13 (⟨25,(20),[1,13],[135],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid699 : RecordDataValid section14Catalog 13 (⟨25,(20),[1,13],[151],173⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨173,[1,2,5,6,9,10,13,14],173⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid700 : RecordDataValid section14Catalog 13 (⟨25,(21),[1,2,5,6,13,14],[146],151⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨151,[1,2,3,5,6,7,13,14,15],151⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid701 : RecordDataValid section14Catalog 13 (⟨25,(21),[1,2,13,14],[131],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid702 : RecordDataValid section14Catalog 13 (⟨25,(21),[1,2,13,14],[147],173⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨173,[1,2,5,6,9,10,13,14],173⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid703 : RecordDataValid section14Catalog 13 (⟨25,(21),[1,2,13,14],[150],199⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨199,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],199⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_0672_0704 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 672).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 672).take 32 = [⟨25,(17),[1,2,5,6,13,14],[146],150⟩,⟨25,(17),[1,2,13,14],[131],35⟩,⟨25,(17),[1,2,13,14],[147],172⟩,⟨25,(17),[1,2,13,14],[150],197⟩,⟨25,(17),[1,2,13,14],[190],221⟩,⟨25,(17),[1,13],[135],35⟩,⟨25,(17),[1,13],[151],172⟩,⟨25,(18),[1,2,5,6,13,14],[146],150⟩,⟨25,(18),[1,2,13,14],[131],35⟩,⟨25,(18),[1,2,13,14],[147],172⟩,⟨25,(18),[1,2,13,14],[150],197⟩,⟨25,(18),[1,2,13,14],[190],221⟩,⟨25,(18),[1,13],[135],35⟩,⟨25,(18),[1,13],[151],172⟩,⟨25,(19),[1,2,5,6,13,14],[146],150⟩,⟨25,(19),[1,2,13,14],[131],35⟩,⟨25,(19),[1,2,13,14],[147],172⟩,⟨25,(19),[1,2,13,14],[150],197⟩,⟨25,(19),[1,2,13,14],[190],221⟩,⟨25,(19),[1,13],[135],35⟩,⟨25,(19),[1,13],[151],172⟩,⟨25,(20),[1,2,5,6,13,14],[146],151⟩,⟨25,(20),[1,2,5,6,13,14],[150],198⟩,⟨25,(20),[1,2,13,14],[131],38⟩,⟨25,(20),[1,2,13,14],[147],173⟩,⟨25,(20),[1,2,13,14],[190],198⟩,⟨25,(20),[1,13],[135],38⟩,⟨25,(20),[1,13],[151],173⟩,⟨25,(21),[1,2,5,6,13,14],[146],151⟩,⟨25,(21),[1,2,13,14],[131],38⟩,⟨25,(21),[1,2,13,14],[147],173⟩,⟨25,(21),[1,2,13,14],[150],199⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid672
  · exact recordValid_of_data section14Catalog 13 _ hnum valid673
  · exact recordValid_of_data section14Catalog 13 _ hnum valid674
  · exact recordValid_of_data section14Catalog 13 _ hnum valid675
  · exact recordValid_of_data section14Catalog 13 _ hnum valid676
  · exact recordValid_of_data section14Catalog 13 _ hnum valid677
  · exact recordValid_of_data section14Catalog 13 _ hnum valid678
  · exact recordValid_of_data section14Catalog 13 _ hnum valid679
  · exact recordValid_of_data section14Catalog 13 _ hnum valid680
  · exact recordValid_of_data section14Catalog 13 _ hnum valid681
  · exact recordValid_of_data section14Catalog 13 _ hnum valid682
  · exact recordValid_of_data section14Catalog 13 _ hnum valid683
  · exact recordValid_of_data section14Catalog 13 _ hnum valid684
  · exact recordValid_of_data section14Catalog 13 _ hnum valid685
  · exact recordValid_of_data section14Catalog 13 _ hnum valid686
  · exact recordValid_of_data section14Catalog 13 _ hnum valid687
  · exact recordValid_of_data section14Catalog 13 _ hnum valid688
  · exact recordValid_of_data section14Catalog 13 _ hnum valid689
  · exact recordValid_of_data section14Catalog 13 _ hnum valid690
  · exact recordValid_of_data section14Catalog 13 _ hnum valid691
  · exact recordValid_of_data section14Catalog 13 _ hnum valid692
  · exact recordValid_of_data section14Catalog 13 _ hnum valid693
  · exact recordValid_of_data section14Catalog 13 _ hnum valid694
  · exact recordValid_of_data section14Catalog 13 _ hnum valid695
  · exact recordValid_of_data section14Catalog 13 _ hnum valid696
  · exact recordValid_of_data section14Catalog 13 _ hnum valid697
  · exact recordValid_of_data section14Catalog 13 _ hnum valid698
  · exact recordValid_of_data section14Catalog 13 _ hnum valid699
  · exact recordValid_of_data section14Catalog 13 _ hnum valid700
  · exact recordValid_of_data section14Catalog 13 _ hnum valid701
  · exact recordValid_of_data section14Catalog 13 _ hnum valid702
  · exact recordValid_of_data section14Catalog 13 _ hnum valid703
end Section14Records_13_672_704

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_0672_0704

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 576).take 128, section14RecordValid section14Catalog 13 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (13 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 13 r
  exact (all_of_interval_split P xs 576 640 704 (by decide) (by decide) (all_of_interval_split P xs 576 608 640 (by decide) (by decide) (Freiman.workReverse20260919_s0013_records_0576_0608 hnum) (Freiman.workReverse20260919_s0013_records_0608_0640 hnum)) (all_of_interval_split P xs 640 672 704 (by decide) (by decide) (Freiman.workReverse20260919_s0013_records_0640_0672 hnum) (Freiman.workReverse20260919_s0013_records_0672_0704 hnum)))

#print axioms solution
