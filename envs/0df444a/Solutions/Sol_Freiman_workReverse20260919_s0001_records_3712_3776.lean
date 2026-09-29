-- Prove2me | solution 1 for Freiman.workReverse20260919_s0001_records_3712_3776
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T03:41:31.318521+00:00
-- url     : https://prove2.me/submissions/3dc91f18-8d4c-4b4b-838c-98a0fcb7065f

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3712_3744
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_3712_3744
private theorem valid3712 : RecordDataValid section14Catalog 1 (⟨235,(2),[1,2,5,6,13,14],[170],580⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨580,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],581⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3713 : RecordDataValid section14Catalog 1 (⟨235,(3),[1,2,5,6,13,14],[170],581⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨581,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],582⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3714 : RecordDataValid section14Catalog 1 (⟨235,(4),[1,2,5,6,13,14],[170],582⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨582,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],583⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3715 : RecordDataValid section14Catalog 1 (⟨235,(5),[1,2,5,6,13,14],[170],583⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨583,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],584⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3716 : RecordDataValid section14Catalog 1 (⟨235,(6),[1,2,5,6,13,14],[170],584⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨584,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],585⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3717 : RecordDataValid section14Catalog 1 (⟨235,(7),[1,2,5,6,13,14],[170],585⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨585,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],586⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3718 : RecordDataValid section14Catalog 1 (⟨235,(8),[1,2,5,6,13,14],[170],578⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨578,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],579⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3719 : RecordDataValid section14Catalog 1 (⟨235,(9),[1,2,5,6,13,14],[170],579⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨579,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],580⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3720 : RecordDataValid section14Catalog 1 (⟨235,(10),[1,2,5,6,13,14],[170],580⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨580,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],581⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3721 : RecordDataValid section14Catalog 1 (⟨235,(11),[1,2,5,6,13,14],[170],581⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨581,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],582⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3722 : RecordDataValid section14Catalog 1 (⟨235,(12),[1,2,5,6,13,14],[170],586⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨586,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],587⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3723 : RecordDataValid section14Catalog 1 (⟨235,(13),[1,2,5,6,13,14],[170],587⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨587,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],588⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3724 : RecordDataValid section14Catalog 1 (⟨235,(14),[1,2,5,6,13,14],[170],588⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨588,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],589⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3725 : RecordDataValid section14Catalog 1 (⟨235,(15),[1,2,5,6,13,14],[170],589⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨589,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],590⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3726 : RecordDataValid section14Catalog 1 (⟨236,(0),[1,2,5,6,13,14],[170],861⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨861,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],862⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3727 : RecordDataValid section14Catalog 1 (⟨236,(1),[1,2,5,6,13,14],[170],862⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨862,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],863⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3728 : RecordDataValid section14Catalog 1 (⟨236,(2),[1,2,6,13,14],[170],863⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨863,[1,2,3,6,7,10,11,13,14,15],864⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3729 : RecordDataValid section14Catalog 1 (⟨236,(3),[1,2,5,6,13,14],[170],864⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨864,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],865⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3730 : RecordDataValid section14Catalog 1 (⟨237,(0),[1,2,5,6,13,14],[170],865⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨865,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],866⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3731 : RecordDataValid section14Catalog 1 (⟨237,(1),[1,2,5,6,13,14],[170],594⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨594,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],595⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3732 : RecordDataValid section14Catalog 1 (⟨237,(2),[1,2,5,6,13,14],[170],595⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨595,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],596⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3733 : RecordDataValid section14Catalog 1 (⟨237,(3),[1,2,5,6,13,14],[170],596⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨596,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],597⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3734 : RecordDataValid section14Catalog 1 (⟨237,(4),[1,2,5,6,13,14],[170],866⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨866,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],867⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3735 : RecordDataValid section14Catalog 1 (⟨237,(5),[1,2,5,6,13,14],[170],598⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨598,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],599⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3736 : RecordDataValid section14Catalog 1 (⟨237,(6),[1,2,5,6,13,14],[170],599⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨599,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],600⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3737 : RecordDataValid section14Catalog 1 (⟨237,(7),[1,2,5,6,13,14],[170],600⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨600,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],601⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3738 : RecordDataValid section14Catalog 1 (⟨237,(8),[1,2,6,13,14],[170],867⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨867,[1,2,3,6,7,10,11,13,14,15],868⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3739 : RecordDataValid section14Catalog 1 (⟨237,(9),[1,2,5,6,13,14],[170],594⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨594,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],595⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3740 : RecordDataValid section14Catalog 1 (⟨237,(10),[1,2,5,6,13,14],[170],595⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨595,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],596⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3741 : RecordDataValid section14Catalog 1 (⟨237,(11),[1,2,5,6,13,14],[170],596⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨596,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],597⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3742 : RecordDataValid section14Catalog 1 (⟨237,(12),[1,2,5,6,13,14],[170],868⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨868,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],869⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3743 : RecordDataValid section14Catalog 1 (⟨237,(13),[1,2,5,6,13,14],[170],602⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨602,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],603⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_3712_3744 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3712).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3712).take 32 = [⟨235,(2),[1,2,5,6,13,14],[170],580⟩,⟨235,(3),[1,2,5,6,13,14],[170],581⟩,⟨235,(4),[1,2,5,6,13,14],[170],582⟩,⟨235,(5),[1,2,5,6,13,14],[170],583⟩,⟨235,(6),[1,2,5,6,13,14],[170],584⟩,⟨235,(7),[1,2,5,6,13,14],[170],585⟩,⟨235,(8),[1,2,5,6,13,14],[170],578⟩,⟨235,(9),[1,2,5,6,13,14],[170],579⟩,⟨235,(10),[1,2,5,6,13,14],[170],580⟩,⟨235,(11),[1,2,5,6,13,14],[170],581⟩,⟨235,(12),[1,2,5,6,13,14],[170],586⟩,⟨235,(13),[1,2,5,6,13,14],[170],587⟩,⟨235,(14),[1,2,5,6,13,14],[170],588⟩,⟨235,(15),[1,2,5,6,13,14],[170],589⟩,⟨236,(0),[1,2,5,6,13,14],[170],861⟩,⟨236,(1),[1,2,5,6,13,14],[170],862⟩,⟨236,(2),[1,2,6,13,14],[170],863⟩,⟨236,(3),[1,2,5,6,13,14],[170],864⟩,⟨237,(0),[1,2,5,6,13,14],[170],865⟩,⟨237,(1),[1,2,5,6,13,14],[170],594⟩,⟨237,(2),[1,2,5,6,13,14],[170],595⟩,⟨237,(3),[1,2,5,6,13,14],[170],596⟩,⟨237,(4),[1,2,5,6,13,14],[170],866⟩,⟨237,(5),[1,2,5,6,13,14],[170],598⟩,⟨237,(6),[1,2,5,6,13,14],[170],599⟩,⟨237,(7),[1,2,5,6,13,14],[170],600⟩,⟨237,(8),[1,2,6,13,14],[170],867⟩,⟨237,(9),[1,2,5,6,13,14],[170],594⟩,⟨237,(10),[1,2,5,6,13,14],[170],595⟩,⟨237,(11),[1,2,5,6,13,14],[170],596⟩,⟨237,(12),[1,2,5,6,13,14],[170],868⟩,⟨237,(13),[1,2,5,6,13,14],[170],602⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3712
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3713
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3714
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3715
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3716
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3717
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3718
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3719
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3720
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3721
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3722
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3723
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3724
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3725
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3726
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3727
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3728
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3729
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3730
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3731
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3732
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3733
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3734
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3735
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3736
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3737
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3738
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3739
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3740
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3741
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3742
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3743
end Section14Records_1_3712_3744

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3712_3744


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3744_3776
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_3744_3776
private theorem valid3744 : RecordDataValid section14Catalog 1 (⟨237,(14),[1,2,5,6,13,14],[170],603⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨603,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],604⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3745 : RecordDataValid section14Catalog 1 (⟨237,(15),[1,2,5,6,13,14],[170],604⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨604,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],605⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3746 : RecordDataValid section14Catalog 1 (⟨238,(0),[1,2,5,6,13,14],[170],869⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨869,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],870⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3747 : RecordDataValid section14Catalog 1 (⟨238,(1),[1,2,5,6,13,14],[170],870⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨870,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],871⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3748 : RecordDataValid section14Catalog 1 (⟨238,(2),[1,2,5,6,13,14],[170],607⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨607,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],608⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3749 : RecordDataValid section14Catalog 1 (⟨238,(3),[1,2,5,6,13,14],[170],871⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨871,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],872⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3750 : RecordDataValid section14Catalog 1 (⟨238,(4),[1,2,5,6,13,14],[170],609⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨609,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],610⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3751 : RecordDataValid section14Catalog 1 (⟨238,(5),[1,2,5,6,13,14],[170],610⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨610,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],611⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3752 : RecordDataValid section14Catalog 1 (⟨238,(6),[1,2,5,6,13,14],[170],611⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨611,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],612⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3753 : RecordDataValid section14Catalog 1 (⟨238,(7),[1,2,5,6,13,14],[170],612⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨612,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],613⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3754 : RecordDataValid section14Catalog 1 (⟨238,(8),[1,2,5,6,13,14],[170],613⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨613,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],614⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3755 : RecordDataValid section14Catalog 1 (⟨238,(9),[1,2,5,6,13,14],[170],614⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨614,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],615⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3756 : RecordDataValid section14Catalog 1 (⟨238,(10),[1,2,5,6,13,14],[170],615⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨615,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],616⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3757 : RecordDataValid section14Catalog 1 (⟨238,(11),[1,2,5,6,13,14],[170],616⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨616,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],617⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3758 : RecordDataValid section14Catalog 1 (⟨238,(12),[1,2,5,6,13,14],[170],617⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨617,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],618⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3759 : RecordDataValid section14Catalog 1 (⟨238,(13),[1,2,5,6,13,14],[170],618⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨618,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],619⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3760 : RecordDataValid section14Catalog 1 (⟨238,(14),[1,2,5,6,13,14],[170],619⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨619,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],620⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3761 : RecordDataValid section14Catalog 1 (⟨238,(15),[1,2,5,6,13,14],[170],620⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨620,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],621⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3762 : RecordDataValid section14Catalog 1 (⟨242,(0),[1,2,5,6],[170],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3763 : RecordDataValid section14Catalog 1 (⟨242,(1),[1,2,5,6],[170],872⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨872,[1,2,4,5,6,8,9,10,12,13,14,16],873⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3764 : RecordDataValid section14Catalog 1 (⟨242,(2),[1,2,5,6],[170],873⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨873,[1,2,3,4,5,6,7,8,9,10,11,12],874⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3765 : RecordDataValid section14Catalog 1 (⟨242,(3),[1,2,5,6],[170],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3766 : RecordDataValid section14Catalog 1 (⟨242,(4),[1,2,5,6],[170],873⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨873,[1,2,3,4,5,6,7,8,9,10,11,12],874⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3767 : RecordDataValid section14Catalog 1 (⟨242,(5),[1,2,5,6],[170],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3768 : RecordDataValid section14Catalog 1 (⟨242,(6),[1,2,5,6],[170],872⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨872,[1,2,4,5,6,8,9,10,12,13,14,16],873⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3769 : RecordDataValid section14Catalog 1 (⟨242,(7),[1,2,5,6],[170],874⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨874,[1,2,4,5,6,8,9,10,12],875⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3770 : RecordDataValid section14Catalog 1 (⟨242,(8),[1,2,5,6],[170],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3771 : RecordDataValid section14Catalog 1 (⟨242,(9),[1,2,5,6],[170],874⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨874,[1,2,4,5,6,8,9,10,12],875⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3772 : RecordDataValid section14Catalog 1 (⟨242,(10),[1,2,5,6],[170],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3773 : RecordDataValid section14Catalog 1 (⟨242,(11),[1,2,5,6],[170],872⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨872,[1,2,4,5,6,8,9,10,12,13,14,16],873⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3774 : RecordDataValid section14Catalog 1 (⟨242,(12),[1,2,5,6],[170],875⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨875,[1,2,4,5,6,8,9,10,12],876⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3775 : RecordDataValid section14Catalog 1 (⟨242,(13),[1,2,5,6],[170],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_3744_3776 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3744).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3744).take 32 = [⟨237,(14),[1,2,5,6,13,14],[170],603⟩,⟨237,(15),[1,2,5,6,13,14],[170],604⟩,⟨238,(0),[1,2,5,6,13,14],[170],869⟩,⟨238,(1),[1,2,5,6,13,14],[170],870⟩,⟨238,(2),[1,2,5,6,13,14],[170],607⟩,⟨238,(3),[1,2,5,6,13,14],[170],871⟩,⟨238,(4),[1,2,5,6,13,14],[170],609⟩,⟨238,(5),[1,2,5,6,13,14],[170],610⟩,⟨238,(6),[1,2,5,6,13,14],[170],611⟩,⟨238,(7),[1,2,5,6,13,14],[170],612⟩,⟨238,(8),[1,2,5,6,13,14],[170],613⟩,⟨238,(9),[1,2,5,6,13,14],[170],614⟩,⟨238,(10),[1,2,5,6,13,14],[170],615⟩,⟨238,(11),[1,2,5,6,13,14],[170],616⟩,⟨238,(12),[1,2,5,6,13,14],[170],617⟩,⟨238,(13),[1,2,5,6,13,14],[170],618⟩,⟨238,(14),[1,2,5,6,13,14],[170],619⟩,⟨238,(15),[1,2,5,6,13,14],[170],620⟩,⟨242,(0),[1,2,5,6],[170],632⟩,⟨242,(1),[1,2,5,6],[170],872⟩,⟨242,(2),[1,2,5,6],[170],873⟩,⟨242,(3),[1,2,5,6],[170],101⟩,⟨242,(4),[1,2,5,6],[170],873⟩,⟨242,(5),[1,2,5,6],[170],632⟩,⟨242,(6),[1,2,5,6],[170],872⟩,⟨242,(7),[1,2,5,6],[170],874⟩,⟨242,(8),[1,2,5,6],[170],101⟩,⟨242,(9),[1,2,5,6],[170],874⟩,⟨242,(10),[1,2,5,6],[170],632⟩,⟨242,(11),[1,2,5,6],[170],872⟩,⟨242,(12),[1,2,5,6],[170],875⟩,⟨242,(13),[1,2,5,6],[170],101⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3744
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3745
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3746
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3747
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3748
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3749
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3750
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3751
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3752
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3753
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3754
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3755
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3756
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3757
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3758
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3759
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3760
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3761
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3762
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3763
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3764
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3765
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3766
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3767
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3768
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3769
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3770
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3771
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3772
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3773
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3774
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3775
end Section14Records_1_3744_3776

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3744_3776

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3712).take 64, section14RecordValid section14Catalog 1 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (1 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 1 r
  exact (all_of_interval_split P xs 3712 3744 3776 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_3712_3744 hnum) (Freiman.workReverse20260919_s0001_records_3744_3776 hnum))

#print axioms solution
