-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_3680_3712
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:50:54.191205+00:00
-- url     : https://prove2.me/submissions/8ee01e5c-5008-4923-b286-d7ae9c627d0e

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
namespace Section14Records_6_3680_3712
private theorem valid3680 : RecordDataValid section14Catalog 6 (⟨235,(6),[5,6],[174],1080⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1080,[3,5,6,7],1084⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3681 : RecordDataValid section14Catalog 6 (⟨235,(7),[1,2,5,6,13,14],[170],585⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨585,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],586⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3682 : RecordDataValid section14Catalog 6 (⟨235,(7),[5,6],[174],1081⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1081,[3,5,6,7],1085⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3683 : RecordDataValid section14Catalog 6 (⟨235,(8),[1,2,5,6,13,14],[170],578⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨578,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],579⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3684 : RecordDataValid section14Catalog 6 (⟨235,(8),[5,6],[174],578⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨578,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],579⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3685 : RecordDataValid section14Catalog 6 (⟨235,(9),[1,2,5,6,13,14],[170],579⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨579,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],580⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3686 : RecordDataValid section14Catalog 6 (⟨235,(9),[5,6],[174],579⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨579,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],580⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3687 : RecordDataValid section14Catalog 6 (⟨235,(10),[1,2,5,6,13,14],[170],580⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨580,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],581⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3688 : RecordDataValid section14Catalog 6 (⟨235,(10),[5,6],[174],1078⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1078,[3,5,6,7],1082⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3689 : RecordDataValid section14Catalog 6 (⟨235,(11),[1,2,5,6,13,14],[170],581⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨581,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],582⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3690 : RecordDataValid section14Catalog 6 (⟨235,(11),[5,6],[174],1079⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1079,[3,5,6,7],1083⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3691 : RecordDataValid section14Catalog 6 (⟨235,(12),[1,2,5,6,13,14],[170],586⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨586,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],587⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3692 : RecordDataValid section14Catalog 6 (⟨235,(12),[5,6],[174],586⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨586,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],587⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3693 : RecordDataValid section14Catalog 6 (⟨235,(13),[1,2,5,6,13,14],[170],587⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨587,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],588⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3694 : RecordDataValid section14Catalog 6 (⟨235,(13),[5,6],[174],587⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨587,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],588⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3695 : RecordDataValid section14Catalog 6 (⟨235,(14),[1,2,5,6,13,14],[170],588⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨588,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],589⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3696 : RecordDataValid section14Catalog 6 (⟨235,(14),[5,6],[174],1082⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1082,[3,5,6,7],1086⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3697 : RecordDataValid section14Catalog 6 (⟨235,(15),[1,2,5,6,13,14],[170],589⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨589,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],590⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3698 : RecordDataValid section14Catalog 6 (⟨235,(15),[5,6],[174],1083⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1083,[3,5,6,7],1087⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3699 : RecordDataValid section14Catalog 6 (⟨236,(0),[1,2,5,6,13,14],[170],861⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨861,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],862⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3700 : RecordDataValid section14Catalog 6 (⟨236,(0),[5,6],[174],861⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨861,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],862⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3701 : RecordDataValid section14Catalog 6 (⟨236,(1),[1,2,5,6,13,14],[170],862⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨862,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],863⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3702 : RecordDataValid section14Catalog 6 (⟨236,(1),[5,6],[174],862⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨862,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],863⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3703 : RecordDataValid section14Catalog 6 (⟨236,(2),[1,2,6,13,14],[170],863⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨863,[1,2,3,6,7,10,11,13,14,15],864⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3704 : RecordDataValid section14Catalog 6 (⟨236,(2),[6],[174],863⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨863,[1,2,3,6,7,10,11,13,14,15],864⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3705 : RecordDataValid section14Catalog 6 (⟨236,(3),[1,2,5,6,13,14],[170],864⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨864,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],865⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3706 : RecordDataValid section14Catalog 6 (⟨236,(3),[5,6],[174],864⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨864,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],865⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3707 : RecordDataValid section14Catalog 6 (⟨237,(0),[1,2,5,6,13,14],[170],865⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨865,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],866⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3708 : RecordDataValid section14Catalog 6 (⟨237,(0),[5,6],[174],865⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨865,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],866⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3709 : RecordDataValid section14Catalog 6 (⟨237,(1),[1,2,5,6,13,14],[170],594⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨594,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],595⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3710 : RecordDataValid section14Catalog 6 (⟨237,(1),[5,6],[174],594⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨594,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],595⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3711 : RecordDataValid section14Catalog 6 (⟨237,(2),[1,2,5,6,13,14],[170],595⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨595,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],596⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3680).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3680).take 32 = [⟨235,(6),[5,6],[174],1080⟩,⟨235,(7),[1,2,5,6,13,14],[170],585⟩,⟨235,(7),[5,6],[174],1081⟩,⟨235,(8),[1,2,5,6,13,14],[170],578⟩,⟨235,(8),[5,6],[174],578⟩,⟨235,(9),[1,2,5,6,13,14],[170],579⟩,⟨235,(9),[5,6],[174],579⟩,⟨235,(10),[1,2,5,6,13,14],[170],580⟩,⟨235,(10),[5,6],[174],1078⟩,⟨235,(11),[1,2,5,6,13,14],[170],581⟩,⟨235,(11),[5,6],[174],1079⟩,⟨235,(12),[1,2,5,6,13,14],[170],586⟩,⟨235,(12),[5,6],[174],586⟩,⟨235,(13),[1,2,5,6,13,14],[170],587⟩,⟨235,(13),[5,6],[174],587⟩,⟨235,(14),[1,2,5,6,13,14],[170],588⟩,⟨235,(14),[5,6],[174],1082⟩,⟨235,(15),[1,2,5,6,13,14],[170],589⟩,⟨235,(15),[5,6],[174],1083⟩,⟨236,(0),[1,2,5,6,13,14],[170],861⟩,⟨236,(0),[5,6],[174],861⟩,⟨236,(1),[1,2,5,6,13,14],[170],862⟩,⟨236,(1),[5,6],[174],862⟩,⟨236,(2),[1,2,6,13,14],[170],863⟩,⟨236,(2),[6],[174],863⟩,⟨236,(3),[1,2,5,6,13,14],[170],864⟩,⟨236,(3),[5,6],[174],864⟩,⟨237,(0),[1,2,5,6,13,14],[170],865⟩,⟨237,(0),[5,6],[174],865⟩,⟨237,(1),[1,2,5,6,13,14],[170],594⟩,⟨237,(1),[5,6],[174],594⟩,⟨237,(2),[1,2,5,6,13,14],[170],595⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3680
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3681
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3682
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3683
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3684
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3685
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3686
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3687
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3688
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3689
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3690
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3691
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3692
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3693
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3694
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3695
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3696
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3697
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3698
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3699
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3700
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3701
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3702
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3703
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3704
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3705
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3706
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3707
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3708
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3709
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3710
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3711
end Section14Records_6_3680_3712

#print axioms solution
