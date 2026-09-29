-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_4000_4032
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:06:20.199989+00:00
-- url     : https://prove2.me/submissions/e5dfb875-b333-4ca4-bf4b-decfc35b1c03

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
namespace Section14Records_5_4000_4032
private theorem valid4000 : RecordDataValid section14Catalog 5 (⟨237,(4),[5,6],[174],866⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨866,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],867⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4001 : RecordDataValid section14Catalog 5 (⟨237,(5),[1,2,5,6,13,14],[170],598⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨598,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],599⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4002 : RecordDataValid section14Catalog 5 (⟨237,(5),[5,6],[174],598⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨598,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],599⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4003 : RecordDataValid section14Catalog 5 (⟨237,(6),[1,2,5,6,13,14],[170],599⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨599,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],600⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4004 : RecordDataValid section14Catalog 5 (⟨237,(6),[5,6],[174],599⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨599,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],600⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4005 : RecordDataValid section14Catalog 5 (⟨237,(7),[1,2,5,6,13,14],[170],600⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨600,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],601⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4006 : RecordDataValid section14Catalog 5 (⟨237,(7),[5,6],[174],600⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨600,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],601⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4007 : RecordDataValid section14Catalog 5 (⟨237,(8),[5],[170,174],865⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨865,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],866⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4008 : RecordDataValid section14Catalog 5 (⟨237,(9),[1,2,5,6,13,14],[170],594⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨594,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],595⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4009 : RecordDataValid section14Catalog 5 (⟨237,(9),[5,6],[174],594⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨594,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],595⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4010 : RecordDataValid section14Catalog 5 (⟨237,(10),[1,2,5,6,13,14],[170],595⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨595,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],596⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4011 : RecordDataValid section14Catalog 5 (⟨237,(10),[5,6],[174],595⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨595,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],596⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4012 : RecordDataValid section14Catalog 5 (⟨237,(11),[1,2,5,6,13,14],[170],596⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨596,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],597⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4013 : RecordDataValid section14Catalog 5 (⟨237,(11),[5,6],[174],596⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨596,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],597⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4014 : RecordDataValid section14Catalog 5 (⟨237,(12),[1,2,5,6,13,14],[170],868⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨868,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],869⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4015 : RecordDataValid section14Catalog 5 (⟨237,(12),[5,6],[174],868⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨868,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],869⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4016 : RecordDataValid section14Catalog 5 (⟨237,(13),[1,2,5,6,13,14],[170],602⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨602,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],603⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4017 : RecordDataValid section14Catalog 5 (⟨237,(13),[5,6],[174],602⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨602,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],603⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4018 : RecordDataValid section14Catalog 5 (⟨237,(14),[1,2,5,6,13,14],[170],603⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨603,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],604⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4019 : RecordDataValid section14Catalog 5 (⟨237,(14),[5,6],[174],603⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨603,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],604⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4020 : RecordDataValid section14Catalog 5 (⟨237,(15),[1,2,5,6,13,14],[170],604⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨604,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],605⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4021 : RecordDataValid section14Catalog 5 (⟨237,(15),[5,6],[174],604⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨604,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],605⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4022 : RecordDataValid section14Catalog 5 (⟨238,(0),[1,2,5,6,13,14],[170],869⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨869,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],870⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4023 : RecordDataValid section14Catalog 5 (⟨238,(0),[5,6],[174],869⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨869,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],870⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4024 : RecordDataValid section14Catalog 5 (⟨238,(1),[1,2,5,6,13,14],[170],870⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨870,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],871⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4025 : RecordDataValid section14Catalog 5 (⟨238,(1),[5,6],[174],870⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨870,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],871⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4026 : RecordDataValid section14Catalog 5 (⟨238,(2),[1,2,5,6,13,14],[170],607⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨607,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],608⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4027 : RecordDataValid section14Catalog 5 (⟨238,(2),[5,6],[174],1084⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1084,[3,5,6,7],1088⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4028 : RecordDataValid section14Catalog 5 (⟨238,(3),[1,2,5,6,13,14],[170],871⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨871,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],872⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4029 : RecordDataValid section14Catalog 5 (⟨238,(3),[5,6],[174],1085⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1085,[3,5,6],1089⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4030 : RecordDataValid section14Catalog 5 (⟨238,(4),[1,2,5,6,13,14],[170],609⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨609,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],610⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4031 : RecordDataValid section14Catalog 5 (⟨238,(4),[5,6],[174],609⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨609,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],610⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4000).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4000).take 32 = [⟨237,(4),[5,6],[174],866⟩,⟨237,(5),[1,2,5,6,13,14],[170],598⟩,⟨237,(5),[5,6],[174],598⟩,⟨237,(6),[1,2,5,6,13,14],[170],599⟩,⟨237,(6),[5,6],[174],599⟩,⟨237,(7),[1,2,5,6,13,14],[170],600⟩,⟨237,(7),[5,6],[174],600⟩,⟨237,(8),[5],[170,174],865⟩,⟨237,(9),[1,2,5,6,13,14],[170],594⟩,⟨237,(9),[5,6],[174],594⟩,⟨237,(10),[1,2,5,6,13,14],[170],595⟩,⟨237,(10),[5,6],[174],595⟩,⟨237,(11),[1,2,5,6,13,14],[170],596⟩,⟨237,(11),[5,6],[174],596⟩,⟨237,(12),[1,2,5,6,13,14],[170],868⟩,⟨237,(12),[5,6],[174],868⟩,⟨237,(13),[1,2,5,6,13,14],[170],602⟩,⟨237,(13),[5,6],[174],602⟩,⟨237,(14),[1,2,5,6,13,14],[170],603⟩,⟨237,(14),[5,6],[174],603⟩,⟨237,(15),[1,2,5,6,13,14],[170],604⟩,⟨237,(15),[5,6],[174],604⟩,⟨238,(0),[1,2,5,6,13,14],[170],869⟩,⟨238,(0),[5,6],[174],869⟩,⟨238,(1),[1,2,5,6,13,14],[170],870⟩,⟨238,(1),[5,6],[174],870⟩,⟨238,(2),[1,2,5,6,13,14],[170],607⟩,⟨238,(2),[5,6],[174],1084⟩,⟨238,(3),[1,2,5,6,13,14],[170],871⟩,⟨238,(3),[5,6],[174],1085⟩,⟨238,(4),[1,2,5,6,13,14],[170],609⟩,⟨238,(4),[5,6],[174],609⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4000
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4001
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4002
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4003
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4004
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4005
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4006
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4007
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4008
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4009
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4010
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4011
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4012
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4013
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4014
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4015
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4016
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4017
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4018
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4019
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4020
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4021
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4022
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4023
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4024
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4025
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4026
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4027
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4028
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4029
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4030
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4031
end Section14Records_5_4000_4032

#print axioms solution
