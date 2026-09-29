-- Prove2me | solution 1 for Freiman.workReverse20260919_s0013_records_2688_2816
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T09:01:04.562617+00:00
-- url     : https://prove2.me/submissions/6c2b8bf0-d821-4b87-b977-2018ad6d7279

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2688_2720
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_2688_2720
private theorem valid2688 : RecordDataValid section14Catalog 13 (⟨235,(3),[1,2,5,6,13,14],[170],581⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨581,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],582⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2689 : RecordDataValid section14Catalog 13 (⟨235,(4),[1,2,5,6,13,14],[170],582⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨582,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],583⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2690 : RecordDataValid section14Catalog 13 (⟨235,(5),[1,2,5,6,13,14],[170],583⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨583,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],584⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2691 : RecordDataValid section14Catalog 13 (⟨235,(6),[1,2,5,6,13,14],[170],584⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨584,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],585⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2692 : RecordDataValid section14Catalog 13 (⟨235,(7),[1,2,5,6,13,14],[170],585⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨585,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],586⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2693 : RecordDataValid section14Catalog 13 (⟨235,(8),[1,2,5,6,13,14],[170],578⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨578,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],579⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2694 : RecordDataValid section14Catalog 13 (⟨235,(9),[1,2,5,6,13,14],[170],579⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨579,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],580⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2695 : RecordDataValid section14Catalog 13 (⟨235,(10),[1,2,5,6,13,14],[170],580⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨580,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],581⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2696 : RecordDataValid section14Catalog 13 (⟨235,(11),[1,2,5,6,13,14],[170],581⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨581,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],582⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2697 : RecordDataValid section14Catalog 13 (⟨235,(12),[1,2,5,6,13,14],[170],586⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨586,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],587⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2698 : RecordDataValid section14Catalog 13 (⟨235,(13),[1,2,5,6,13,14],[170],587⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨587,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],588⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2699 : RecordDataValid section14Catalog 13 (⟨235,(14),[1,2,5,6,13,14],[170],588⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨588,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],589⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2700 : RecordDataValid section14Catalog 13 (⟨235,(15),[1,2,5,6,13,14],[170],589⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨589,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],590⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2701 : RecordDataValid section14Catalog 13 (⟨236,(0),[1,2,5,6,13,14],[170],861⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨861,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],862⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2702 : RecordDataValid section14Catalog 13 (⟨236,(1),[1,2,5,6,13,14],[170],862⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨862,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],863⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2703 : RecordDataValid section14Catalog 13 (⟨236,(2),[1,2,6,13,14],[170],863⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨863,[1,2,3,6,7,10,11,13,14,15],864⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2704 : RecordDataValid section14Catalog 13 (⟨236,(3),[1,2,5,6,13,14],[170],864⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨864,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],865⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2705 : RecordDataValid section14Catalog 13 (⟨237,(0),[1,2,5,6,13,14],[170],865⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨865,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],866⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2706 : RecordDataValid section14Catalog 13 (⟨237,(1),[1,2,5,6,13,14],[170],594⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨594,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],595⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2707 : RecordDataValid section14Catalog 13 (⟨237,(2),[1,2,5,6,13,14],[170],595⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨595,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],596⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2708 : RecordDataValid section14Catalog 13 (⟨237,(3),[1,2,5,6,13,14],[170],596⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨596,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],597⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2709 : RecordDataValid section14Catalog 13 (⟨237,(4),[1,2,5,6,13,14],[170],866⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨866,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],867⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2710 : RecordDataValid section14Catalog 13 (⟨237,(5),[1,2,5,6,13,14],[170],598⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨598,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],599⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2711 : RecordDataValid section14Catalog 13 (⟨237,(6),[1,2,5,6,13,14],[170],599⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨599,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],600⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2712 : RecordDataValid section14Catalog 13 (⟨237,(7),[1,2,5,6,13,14],[170],600⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨600,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],601⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2713 : RecordDataValid section14Catalog 13 (⟨237,(8),[1,2,6,13,14],[170],867⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨867,[1,2,3,6,7,10,11,13,14,15],868⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2714 : RecordDataValid section14Catalog 13 (⟨237,(9),[1,2,5,6,13,14],[170],594⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨594,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],595⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2715 : RecordDataValid section14Catalog 13 (⟨237,(10),[1,2,5,6,13,14],[170],595⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨595,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],596⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2716 : RecordDataValid section14Catalog 13 (⟨237,(11),[1,2,5,6,13,14],[170],596⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨596,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],597⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2717 : RecordDataValid section14Catalog 13 (⟨237,(12),[1,2,5,6,13,14],[170],868⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨868,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],869⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2718 : RecordDataValid section14Catalog 13 (⟨237,(13),[1,2,5,6,13,14],[170],602⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨602,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],603⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2719 : RecordDataValid section14Catalog 13 (⟨237,(14),[1,2,5,6,13,14],[170],603⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨603,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],604⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_2688_2720 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2688).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2688).take 32 = [⟨235,(3),[1,2,5,6,13,14],[170],581⟩,⟨235,(4),[1,2,5,6,13,14],[170],582⟩,⟨235,(5),[1,2,5,6,13,14],[170],583⟩,⟨235,(6),[1,2,5,6,13,14],[170],584⟩,⟨235,(7),[1,2,5,6,13,14],[170],585⟩,⟨235,(8),[1,2,5,6,13,14],[170],578⟩,⟨235,(9),[1,2,5,6,13,14],[170],579⟩,⟨235,(10),[1,2,5,6,13,14],[170],580⟩,⟨235,(11),[1,2,5,6,13,14],[170],581⟩,⟨235,(12),[1,2,5,6,13,14],[170],586⟩,⟨235,(13),[1,2,5,6,13,14],[170],587⟩,⟨235,(14),[1,2,5,6,13,14],[170],588⟩,⟨235,(15),[1,2,5,6,13,14],[170],589⟩,⟨236,(0),[1,2,5,6,13,14],[170],861⟩,⟨236,(1),[1,2,5,6,13,14],[170],862⟩,⟨236,(2),[1,2,6,13,14],[170],863⟩,⟨236,(3),[1,2,5,6,13,14],[170],864⟩,⟨237,(0),[1,2,5,6,13,14],[170],865⟩,⟨237,(1),[1,2,5,6,13,14],[170],594⟩,⟨237,(2),[1,2,5,6,13,14],[170],595⟩,⟨237,(3),[1,2,5,6,13,14],[170],596⟩,⟨237,(4),[1,2,5,6,13,14],[170],866⟩,⟨237,(5),[1,2,5,6,13,14],[170],598⟩,⟨237,(6),[1,2,5,6,13,14],[170],599⟩,⟨237,(7),[1,2,5,6,13,14],[170],600⟩,⟨237,(8),[1,2,6,13,14],[170],867⟩,⟨237,(9),[1,2,5,6,13,14],[170],594⟩,⟨237,(10),[1,2,5,6,13,14],[170],595⟩,⟨237,(11),[1,2,5,6,13,14],[170],596⟩,⟨237,(12),[1,2,5,6,13,14],[170],868⟩,⟨237,(13),[1,2,5,6,13,14],[170],602⟩,⟨237,(14),[1,2,5,6,13,14],[170],603⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2688
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2689
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2690
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2691
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2692
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2693
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2694
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2695
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2696
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2697
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2698
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2699
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2700
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2701
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2702
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2703
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2704
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2705
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2706
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2707
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2708
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2709
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2710
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2711
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2712
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2713
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2714
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2715
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2716
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2717
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2718
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2719
end Section14Records_13_2688_2720

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2688_2720


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2720_2752
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_2720_2752
private theorem valid2720 : RecordDataValid section14Catalog 13 (⟨237,(15),[1,2,5,6,13,14],[170],604⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨604,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],605⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2721 : RecordDataValid section14Catalog 13 (⟨238,(0),[1,2,5,6,13,14],[170],869⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨869,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],870⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2722 : RecordDataValid section14Catalog 13 (⟨238,(1),[1,2,5,6,13,14],[170],870⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨870,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],871⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2723 : RecordDataValid section14Catalog 13 (⟨238,(2),[1,2,5,6,13,14],[170],607⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨607,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],608⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2724 : RecordDataValid section14Catalog 13 (⟨238,(3),[1,2,5,6,13,14],[170],871⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨871,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],872⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2725 : RecordDataValid section14Catalog 13 (⟨238,(4),[1,2,5,6,13,14],[170],609⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨609,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],610⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2726 : RecordDataValid section14Catalog 13 (⟨238,(5),[1,2,5,6,13,14],[170],610⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨610,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],611⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2727 : RecordDataValid section14Catalog 13 (⟨238,(6),[1,2,5,6,13,14],[170],611⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨611,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],612⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2728 : RecordDataValid section14Catalog 13 (⟨238,(7),[1,2,5,6,13,14],[170],612⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨612,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],613⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2729 : RecordDataValid section14Catalog 13 (⟨238,(8),[1,2,5,6,13,14],[170],613⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨613,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],614⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2730 : RecordDataValid section14Catalog 13 (⟨238,(9),[1,2,5,6,13,14],[170],614⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨614,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],615⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2731 : RecordDataValid section14Catalog 13 (⟨238,(10),[1,2,5,6,13,14],[170],615⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨615,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],616⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2732 : RecordDataValid section14Catalog 13 (⟨238,(11),[1,2,5,6,13,14],[170],616⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨616,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],617⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2733 : RecordDataValid section14Catalog 13 (⟨238,(12),[1,2,5,6,13,14],[170],617⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨617,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],618⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2734 : RecordDataValid section14Catalog 13 (⟨238,(13),[1,2,5,6,13,14],[170],618⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨618,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],619⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2735 : RecordDataValid section14Catalog 13 (⟨238,(14),[1,2,5,6,13,14],[170],619⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨619,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],620⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2736 : RecordDataValid section14Catalog 13 (⟨238,(15),[1,2,5,6,13,14],[170],620⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨620,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],621⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2737 : RecordDataValid section14Catalog 13 (⟨243,(5),[13],[170],105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨105,[1,2,3,5,6,7,13,14,15],105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2738 : RecordDataValid section14Catalog 13 (⟨243,(7),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2739 : RecordDataValid section14Catalog 13 (⟨243,(8),[1,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2740 : RecordDataValid section14Catalog 13 (⟨243,(9),[5,6,13,14],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2741 : RecordDataValid section14Catalog 13 (⟨243,(15),[5,13],[170],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2742 : RecordDataValid section14Catalog 13 (⟨243,(16),[1,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2743 : RecordDataValid section14Catalog 13 (⟨243,(17),[1,2,5,6,13,14],[170],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2744 : RecordDataValid section14Catalog 13 (⟨243,(19),[1,13],[170],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2745 : RecordDataValid section14Catalog 13 (⟨245,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2746 : RecordDataValid section14Catalog 13 (⟨245,(-1),[1,2,5,6,9,10,13,14],[1,5],881⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨881,[1,2,3,5,6,7,9,10,11,13,14,15],883⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2747 : RecordDataValid section14Catalog 13 (⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2748 : RecordDataValid section14Catalog 13 (⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2749 : RecordDataValid section14Catalog 13 (⟨245,(-1),[1,2,5,6,13,14],[17,21,41,45,57,61],881⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨881,[1,2,3,5,6,7,9,10,11,13,14,15],883⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2750 : RecordDataValid section14Catalog 13 (⟨245,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2751 : RecordDataValid section14Catalog 13 (⟨245,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],883⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨883,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],885⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_2720_2752 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2720).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2720).take 32 = [⟨237,(15),[1,2,5,6,13,14],[170],604⟩,⟨238,(0),[1,2,5,6,13,14],[170],869⟩,⟨238,(1),[1,2,5,6,13,14],[170],870⟩,⟨238,(2),[1,2,5,6,13,14],[170],607⟩,⟨238,(3),[1,2,5,6,13,14],[170],871⟩,⟨238,(4),[1,2,5,6,13,14],[170],609⟩,⟨238,(5),[1,2,5,6,13,14],[170],610⟩,⟨238,(6),[1,2,5,6,13,14],[170],611⟩,⟨238,(7),[1,2,5,6,13,14],[170],612⟩,⟨238,(8),[1,2,5,6,13,14],[170],613⟩,⟨238,(9),[1,2,5,6,13,14],[170],614⟩,⟨238,(10),[1,2,5,6,13,14],[170],615⟩,⟨238,(11),[1,2,5,6,13,14],[170],616⟩,⟨238,(12),[1,2,5,6,13,14],[170],617⟩,⟨238,(13),[1,2,5,6,13,14],[170],618⟩,⟨238,(14),[1,2,5,6,13,14],[170],619⟩,⟨238,(15),[1,2,5,6,13,14],[170],620⟩,⟨243,(5),[13],[170],105⟩,⟨243,(7),[1,2,5,6,13,14],[170],3⟩,⟨243,(8),[1,5,6,13,14],[170],3⟩,⟨243,(9),[5,6,13,14],[170],143⟩,⟨243,(15),[5,13],[170],48⟩,⟨243,(16),[1,5,6,13,14],[170],3⟩,⟨243,(17),[1,2,5,6,13,14],[170],48⟩,⟨243,(19),[1,13],[170],48⟩,⟨245,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩,⟨245,(-1),[1,2,5,6,9,10,13,14],[1,5],881⟩,⟨245,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩,⟨245,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩,⟨245,(-1),[1,2,5,6,13,14],[17,21,41,45,57,61],881⟩,⟨245,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],882⟩,⟨245,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],883⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2720
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2721
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2722
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2723
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2724
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2725
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2726
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2727
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2728
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2729
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2730
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2731
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2732
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2733
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2734
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2735
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2736
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2737
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2738
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2739
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2740
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2741
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2742
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2743
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2744
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2745
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2746
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2747
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2748
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2749
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2750
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2751
end Section14Records_13_2720_2752

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2720_2752


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2752_2784
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_2752_2784
private theorem valid2752 : RecordDataValid section14Catalog 13 (⟨245,(-1),[1,2,5,6,13,14],[130,134],884⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨884,[1,2,4,5,6,8,9,10,12,13,14,16],886⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2753 : RecordDataValid section14Catalog 13 (⟨245,(-1),[1,2,5,6,13,14],[146],885⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨885,[1,2,3,5,6,7,13,14,15],887⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2754 : RecordDataValid section14Catalog 13 (⟨245,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],886⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨886,[1,2,4,5,6,8,9,10,12,13,14,16],888⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2755 : RecordDataValid section14Catalog 13 (⟨245,(-1),[1,2,5,6,13,14],[150],887⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨887,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],889⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2756 : RecordDataValid section14Catalog 13 (⟨245,(-1),[1,2,5,6,13,14],[174],908⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨908,[1,2,3,5,6,7,13,14,15],910⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2757 : RecordDataValid section14Catalog 13 (⟨245,(-1),[1,2,5,6,13,14],[186],909⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨909,[1,2,4,5,6,8,9,10,12,13,14,16],911⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2758 : RecordDataValid section14Catalog 13 (⟨245,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],910⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨910,[1,2,3,5,6,7,9,10,11,13,14,15],912⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2759 : RecordDataValid section14Catalog 13 (⟨245,(-1),[1,2,13,14],[131,135],884⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨884,[1,2,4,5,6,8,9,10,12,13,14,16],886⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2760 : RecordDataValid section14Catalog 13 (⟨245,(-1),[1,5,6,13],[194,198],910⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨910,[1,2,3,5,6,7,9,10,11,13,14,15],912⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2761 : RecordDataValid section14Catalog 13 (⟨245,(-1),[1,5,9,13],[0,4],881⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨881,[1,2,3,5,6,7,9,10,11,13,14,15],883⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2762 : RecordDataValid section14Catalog 13 (⟨245,(-1),[1,5,13],[16,20,40,44,56,60],881⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨881,[1,2,3,5,6,7,9,10,11,13,14,15],883⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2763 : RecordDataValid section14Catalog 13 (⟨245,(-1),[1,5,13],[195,199,211,215,235,239,251,255],910⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨910,[1,2,3,5,6,7,9,10,11,13,14,15],912⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2764 : RecordDataValid section14Catalog 13 (⟨245,(-1),[9,10,13],[10,11,14,15,26,27,30,31],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2765 : RecordDataValid section14Catalog 13 (⟨245,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2766 : RecordDataValid section14Catalog 13 (⟨245,(-1),[13],[190],908⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨908,[1,2,3,5,6,7,13,14,15],910⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2767 : RecordDataValid section14Catalog 13 (⟨247,(0),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2768 : RecordDataValid section14Catalog 13 (⟨247,(1),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2769 : RecordDataValid section14Catalog 13 (⟨247,(2),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2770 : RecordDataValid section14Catalog 13 (⟨247,(3),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2771 : RecordDataValid section14Catalog 13 (⟨247,(4),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2772 : RecordDataValid section14Catalog 13 (⟨247,(5),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2773 : RecordDataValid section14Catalog 13 (⟨247,(6),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2774 : RecordDataValid section14Catalog 13 (⟨247,(7),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2775 : RecordDataValid section14Catalog 13 (⟨247,(8),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2776 : RecordDataValid section14Catalog 13 (⟨247,(9),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2777 : RecordDataValid section14Catalog 13 (⟨247,(10),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2778 : RecordDataValid section14Catalog 13 (⟨247,(11),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2779 : RecordDataValid section14Catalog 13 (⟨247,(12),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2780 : RecordDataValid section14Catalog 13 (⟨247,(13),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2781 : RecordDataValid section14Catalog 13 (⟨247,(14),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2782 : RecordDataValid section14Catalog 13 (⟨247,(15),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2783 : RecordDataValid section14Catalog 13 (⟨247,(16),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_2752_2784 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2752).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2752).take 32 = [⟨245,(-1),[1,2,5,6,13,14],[130,134],884⟩,⟨245,(-1),[1,2,5,6,13,14],[146],885⟩,⟨245,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],886⟩,⟨245,(-1),[1,2,5,6,13,14],[150],887⟩,⟨245,(-1),[1,2,5,6,13,14],[174],908⟩,⟨245,(-1),[1,2,5,6,13,14],[186],909⟩,⟨245,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],910⟩,⟨245,(-1),[1,2,13,14],[131,135],884⟩,⟨245,(-1),[1,5,6,13],[194,198],910⟩,⟨245,(-1),[1,5,9,13],[0,4],881⟩,⟨245,(-1),[1,5,13],[16,20,40,44,56,60],881⟩,⟨245,(-1),[1,5,13],[195,199,211,215,235,239,251,255],910⟩,⟨245,(-1),[9,10,13],[10,11,14,15,26,27,30,31],2⟩,⟨245,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩,⟨245,(-1),[13],[190],908⟩,⟨247,(0),[1,2,5,6,13,14],[170],3⟩,⟨247,(1),[1,2,5,6,13,14],[170],3⟩,⟨247,(2),[1,2,5,6,13,14],[170],3⟩,⟨247,(3),[1,2,5,6,13,14],[170],3⟩,⟨247,(4),[1,2,5,6,13,14],[170],3⟩,⟨247,(5),[1,2,5,6,13,14],[170],3⟩,⟨247,(6),[1,2,5,6,13,14],[170],3⟩,⟨247,(7),[1,2,5,6,13,14],[170],3⟩,⟨247,(8),[1,2,5,6,13,14],[170],3⟩,⟨247,(9),[1,2,5,6,13,14],[170],3⟩,⟨247,(10),[1,2,5,6,13,14],[170],3⟩,⟨247,(11),[1,2,5,6,13,14],[170],3⟩,⟨247,(12),[1,2,5,6,13,14],[170],3⟩,⟨247,(13),[1,2,5,6,13,14],[170],3⟩,⟨247,(14),[1,2,5,6,13,14],[170],3⟩,⟨247,(15),[1,2,5,6,13,14],[170],3⟩,⟨247,(16),[1,2,5,6,13,14],[170],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2752
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2753
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2754
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2755
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2756
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2757
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2758
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2759
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2760
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2761
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2762
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2763
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2764
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2765
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2766
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2767
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2768
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2769
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2770
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2771
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2772
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2773
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2774
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2775
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2776
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2777
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2778
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2779
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2780
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2781
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2782
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2783
end Section14Records_13_2752_2784

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2752_2784


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2784_2816
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_2784_2816
private theorem valid2784 : RecordDataValid section14Catalog 13 (⟨247,(17),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2785 : RecordDataValid section14Catalog 13 (⟨247,(18),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2786 : RecordDataValid section14Catalog 13 (⟨247,(19),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2787 : RecordDataValid section14Catalog 13 (⟨247,(20),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2788 : RecordDataValid section14Catalog 13 (⟨247,(21),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2789 : RecordDataValid section14Catalog 13 (⟨247,(22),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2790 : RecordDataValid section14Catalog 13 (⟨247,(23),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2791 : RecordDataValid section14Catalog 13 (⟨247,(24),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2792 : RecordDataValid section14Catalog 13 (⟨249,(0),[1,2,5,6,13,14],[170],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2793 : RecordDataValid section14Catalog 13 (⟨249,(1),[1,13],[170],11⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨11,[1,2,3,4,5,6,7,8,13,14,15,16],11⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2794 : RecordDataValid section14Catalog 13 (⟨249,(2),[1,2,5,6,13,14],[170],888⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨888,[1,2,3,4,5,6,7,8,13,14,15,16],890⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2795 : RecordDataValid section14Catalog 13 (⟨249,(3),[1,2,5,6,13,14],[170],889⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨889,[1,2,3,4,5,6,7,8,13,14,15,16],891⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2796 : RecordDataValid section14Catalog 13 (⟨249,(4),[1,2,5,6,13,14],[170],890⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨890,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],892⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2797 : RecordDataValid section14Catalog 13 (⟨249,(5),[1,2,5,6,13,14],[170],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2798 : RecordDataValid section14Catalog 13 (⟨249,(6),[1,13],[170],11⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨11,[1,2,3,4,5,6,7,8,13,14,15,16],11⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2799 : RecordDataValid section14Catalog 13 (⟨249,(7),[1,2,5,6,13,14],[170],888⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨888,[1,2,3,4,5,6,7,8,13,14,15,16],890⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2800 : RecordDataValid section14Catalog 13 (⟨249,(8),[1,2,5,6,13,14],[170],889⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨889,[1,2,3,4,5,6,7,8,13,14,15,16],891⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2801 : RecordDataValid section14Catalog 13 (⟨249,(9),[1,2,5,6,13,14],[170],890⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨890,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],892⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2802 : RecordDataValid section14Catalog 13 (⟨249,(10),[1,2,5,6,13,14],[170],18⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨18,[1,2,3,4,5,6,7,8,13,14,15,16],18⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2803 : RecordDataValid section14Catalog 13 (⟨249,(11),[1,13],[170],19⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨19,[1,2,3,4,5,6,7,8,13,14,15,16],19⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2804 : RecordDataValid section14Catalog 13 (⟨249,(12),[1,2,5,6,13,14],[170],891⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨891,[1,2,3,4,5,6,7,8,13,14,15,16],893⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2805 : RecordDataValid section14Catalog 13 (⟨249,(13),[1,2,5,6,13,14],[170],891⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨891,[1,2,3,4,5,6,7,8,13,14,15,16],893⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2806 : RecordDataValid section14Catalog 13 (⟨249,(14),[1,2,5,6,13,14],[170],890⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨890,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],892⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2807 : RecordDataValid section14Catalog 13 (⟨249,(15),[1,2,5,6,13,14],[170],21⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨21,[1,2,3,4,5,6,7,8,13,14,15,16],21⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2808 : RecordDataValid section14Catalog 13 (⟨249,(16),[1,13],[170],22⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨22,[1,2,3,4,5,6,7,8,13,14,15,16],22⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2809 : RecordDataValid section14Catalog 13 (⟨249,(17),[1,2,5,6,13,14],[170],892⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨892,[1,2,3,4,5,6,7,8,13,14,15,16],894⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2810 : RecordDataValid section14Catalog 13 (⟨249,(18),[1,2,5,6,13,14],[170],892⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨892,[1,2,3,4,5,6,7,8,13,14,15,16],894⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2811 : RecordDataValid section14Catalog 13 (⟨249,(19),[1,2,5,6,13,14],[170],892⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨892,[1,2,3,4,5,6,7,8,13,14,15,16],894⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2812 : RecordDataValid section14Catalog 13 (⟨249,(20),[1,2,5,6,13,14],[170],24⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨24,[1,2,3,4,5,6,7,8,13,14,15,16],24⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2813 : RecordDataValid section14Catalog 13 (⟨249,(21),[1,13],[170],25⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨25,[1,2,3,4,5,6,7,8,13,14,15,16],25⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2814 : RecordDataValid section14Catalog 13 (⟨249,(22),[1,2,5,6,13,14],[170],893⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨893,[1,2,3,4,5,6,7,8,13,14,15,16],895⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2815 : RecordDataValid section14Catalog 13 (⟨249,(23),[1,2,5,6,13,14],[170],893⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨893,[1,2,3,4,5,6,7,8,13,14,15,16],895⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_2784_2816 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2784).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2784).take 32 = [⟨247,(17),[1,2,5,6,13,14],[170],3⟩,⟨247,(18),[1,2,5,6,13,14],[170],3⟩,⟨247,(19),[1,2,5,6,13,14],[170],3⟩,⟨247,(20),[1,2,5,6,13,14],[170],3⟩,⟨247,(21),[1,2,5,6,13,14],[170],3⟩,⟨247,(22),[1,2,5,6,13,14],[170],3⟩,⟨247,(23),[1,2,5,6,13,14],[170],3⟩,⟨247,(24),[1,2,5,6,13,14],[170],3⟩,⟨249,(0),[1,2,5,6,13,14],[170],10⟩,⟨249,(1),[1,13],[170],11⟩,⟨249,(2),[1,2,5,6,13,14],[170],888⟩,⟨249,(3),[1,2,5,6,13,14],[170],889⟩,⟨249,(4),[1,2,5,6,13,14],[170],890⟩,⟨249,(5),[1,2,5,6,13,14],[170],10⟩,⟨249,(6),[1,13],[170],11⟩,⟨249,(7),[1,2,5,6,13,14],[170],888⟩,⟨249,(8),[1,2,5,6,13,14],[170],889⟩,⟨249,(9),[1,2,5,6,13,14],[170],890⟩,⟨249,(10),[1,2,5,6,13,14],[170],18⟩,⟨249,(11),[1,13],[170],19⟩,⟨249,(12),[1,2,5,6,13,14],[170],891⟩,⟨249,(13),[1,2,5,6,13,14],[170],891⟩,⟨249,(14),[1,2,5,6,13,14],[170],890⟩,⟨249,(15),[1,2,5,6,13,14],[170],21⟩,⟨249,(16),[1,13],[170],22⟩,⟨249,(17),[1,2,5,6,13,14],[170],892⟩,⟨249,(18),[1,2,5,6,13,14],[170],892⟩,⟨249,(19),[1,2,5,6,13,14],[170],892⟩,⟨249,(20),[1,2,5,6,13,14],[170],24⟩,⟨249,(21),[1,13],[170],25⟩,⟨249,(22),[1,2,5,6,13,14],[170],893⟩,⟨249,(23),[1,2,5,6,13,14],[170],893⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2784
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2785
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2786
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2787
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2788
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2789
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2790
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2791
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2792
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2793
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2794
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2795
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2796
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2797
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2798
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2799
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2800
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2801
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2802
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2803
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2804
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2805
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2806
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2807
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2808
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2809
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2810
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2811
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2812
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2813
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2814
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2815
end Section14Records_13_2784_2816

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2784_2816

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2688).take 128, section14RecordValid section14Catalog 13 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (13 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 13 r
  exact (all_of_interval_split P xs 2688 2752 2816 (by decide) (by decide) (all_of_interval_split P xs 2688 2720 2752 (by decide) (by decide) (Freiman.workReverse20260919_s0013_records_2688_2720 hnum) (Freiman.workReverse20260919_s0013_records_2720_2752 hnum)) (all_of_interval_split P xs 2752 2784 2816 (by decide) (by decide) (Freiman.workReverse20260919_s0013_records_2752_2784 hnum) (Freiman.workReverse20260919_s0013_records_2784_2816 hnum)))

#print axioms solution
