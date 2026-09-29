-- Prove2me | solution 1 for Freiman.workReverse20260919_s0001_records_3008_3136
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T02:13:40.610984+00:00
-- url     : https://prove2.me/submissions/2a347564-09df-4a0c-b235-ed3ca3504273

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3008_3040
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_3008_3040
private theorem valid3008 : RecordDataValid section14Catalog 1 (⟨157,(1),[1,2,5,6,13,14],[170],393⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨393,[1,2,3,4,5,6,7,8,13,14,15,16],394⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3009 : RecordDataValid section14Catalog 1 (⟨157,(2),[1,2,5,6,13,14],[170],394⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨394,[1,2,3,4,5,6,7,8,13,14,15,16],395⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3010 : RecordDataValid section14Catalog 1 (⟨157,(3),[1,2,5,6,13,14],[170],395⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨395,[1,2,3,4,5,6,7,8,13,14,15,16],396⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3011 : RecordDataValid section14Catalog 1 (⟨157,(4),[1,2,5,6,13,14],[170],396⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨396,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],397⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3012 : RecordDataValid section14Catalog 1 (⟨157,(5),[1,2,5,6,13,14],[170],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3013 : RecordDataValid section14Catalog 1 (⟨157,(6),[1,2,5,6,13,14],[170],393⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨393,[1,2,3,4,5,6,7,8,13,14,15,16],394⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3014 : RecordDataValid section14Catalog 1 (⟨157,(7),[1,2,5,6,13,14],[170],394⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨394,[1,2,3,4,5,6,7,8,13,14,15,16],395⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3015 : RecordDataValid section14Catalog 1 (⟨157,(8),[1,2,5,6,13,14],[170],395⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨395,[1,2,3,4,5,6,7,8,13,14,15,16],396⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3016 : RecordDataValid section14Catalog 1 (⟨157,(9),[1,2,5,6,13,14],[170],396⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨396,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],397⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3017 : RecordDataValid section14Catalog 1 (⟨157,(10),[1,2,5,6,13,14],[170],18⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨18,[1,2,3,4,5,6,7,8,13,14,15,16],18⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3018 : RecordDataValid section14Catalog 1 (⟨157,(11),[1,2,5,6,13,14],[170],397⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨397,[1,2,3,4,5,6,7,8,13,14,15,16],398⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3019 : RecordDataValid section14Catalog 1 (⟨157,(12),[1,2,5,6,13,14],[170],397⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨397,[1,2,3,4,5,6,7,8,13,14,15,16],398⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3020 : RecordDataValid section14Catalog 1 (⟨157,(13),[1,2,5,6,13,14],[170],397⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨397,[1,2,3,4,5,6,7,8,13,14,15,16],398⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3021 : RecordDataValid section14Catalog 1 (⟨157,(14),[1,2,5,6,13,14],[170],396⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨396,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],397⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3022 : RecordDataValid section14Catalog 1 (⟨157,(15),[1,2,5,6,13,14],[170],21⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨21,[1,2,3,4,5,6,7,8,13,14,15,16],21⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3023 : RecordDataValid section14Catalog 1 (⟨157,(16),[1,2,5,6,13,14],[170],398⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨398,[1,2,3,4,5,6,7,8,13,14,15,16],399⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3024 : RecordDataValid section14Catalog 1 (⟨157,(17),[1,2,5,6,13,14],[170],398⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨398,[1,2,3,4,5,6,7,8,13,14,15,16],399⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3025 : RecordDataValid section14Catalog 1 (⟨157,(18),[1,2,5,6,13,14],[170],398⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨398,[1,2,3,4,5,6,7,8,13,14,15,16],399⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3026 : RecordDataValid section14Catalog 1 (⟨157,(19),[1,2,5,6,13,14],[170],398⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨398,[1,2,3,4,5,6,7,8,13,14,15,16],399⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3027 : RecordDataValid section14Catalog 1 (⟨157,(20),[1,2,5,6,13,14],[170],24⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨24,[1,2,3,4,5,6,7,8,13,14,15,16],24⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3028 : RecordDataValid section14Catalog 1 (⟨157,(21),[1,2,5,6,13,14],[170],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3029 : RecordDataValid section14Catalog 1 (⟨157,(22),[1,2,5,6,13,14],[170],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3030 : RecordDataValid section14Catalog 1 (⟨157,(23),[1,2,5,6,13,14],[170],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3031 : RecordDataValid section14Catalog 1 (⟨157,(24),[1,2,5,6,13,14],[170],399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3032 : RecordDataValid section14Catalog 1 (⟨160,(0),[1,2,5,6,13,14],[170],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3033 : RecordDataValid section14Catalog 1 (⟨160,(1),[1,2,5,6,13,14],[170],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3034 : RecordDataValid section14Catalog 1 (⟨160,(2),[1,2,5,6,13,14],[170],640⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨640,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],641⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3035 : RecordDataValid section14Catalog 1 (⟨160,(3),[1,2,5,6,13,14],[170],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3036 : RecordDataValid section14Catalog 1 (⟨160,(4),[1,2,5,6,13,14],[170],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3037 : RecordDataValid section14Catalog 1 (⟨160,(5),[1,2,5,6,13,14],[170],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3038 : RecordDataValid section14Catalog 1 (⟨160,(6),[1,2,5,6,13,14],[170],642⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨642,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],643⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3039 : RecordDataValid section14Catalog 1 (⟨160,(7),[1,2,5,6,13,14],[170],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_3008_3040 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3008).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3008).take 32 = [⟨157,(1),[1,2,5,6,13,14],[170],393⟩,⟨157,(2),[1,2,5,6,13,14],[170],394⟩,⟨157,(3),[1,2,5,6,13,14],[170],395⟩,⟨157,(4),[1,2,5,6,13,14],[170],396⟩,⟨157,(5),[1,2,5,6,13,14],[170],10⟩,⟨157,(6),[1,2,5,6,13,14],[170],393⟩,⟨157,(7),[1,2,5,6,13,14],[170],394⟩,⟨157,(8),[1,2,5,6,13,14],[170],395⟩,⟨157,(9),[1,2,5,6,13,14],[170],396⟩,⟨157,(10),[1,2,5,6,13,14],[170],18⟩,⟨157,(11),[1,2,5,6,13,14],[170],397⟩,⟨157,(12),[1,2,5,6,13,14],[170],397⟩,⟨157,(13),[1,2,5,6,13,14],[170],397⟩,⟨157,(14),[1,2,5,6,13,14],[170],396⟩,⟨157,(15),[1,2,5,6,13,14],[170],21⟩,⟨157,(16),[1,2,5,6,13,14],[170],398⟩,⟨157,(17),[1,2,5,6,13,14],[170],398⟩,⟨157,(18),[1,2,5,6,13,14],[170],398⟩,⟨157,(19),[1,2,5,6,13,14],[170],398⟩,⟨157,(20),[1,2,5,6,13,14],[170],24⟩,⟨157,(21),[1,2,5,6,13,14],[170],399⟩,⟨157,(22),[1,2,5,6,13,14],[170],399⟩,⟨157,(23),[1,2,5,6,13,14],[170],399⟩,⟨157,(24),[1,2,5,6,13,14],[170],399⟩,⟨160,(0),[1,2,5,6,13,14],[170],638⟩,⟨160,(1),[1,2,5,6,13,14],[170],639⟩,⟨160,(2),[1,2,5,6,13,14],[170],640⟩,⟨160,(3),[1,2,5,6,13,14],[170],641⟩,⟨160,(4),[1,2,5,6,13,14],[170],638⟩,⟨160,(5),[1,2,5,6,13,14],[170],639⟩,⟨160,(6),[1,2,5,6,13,14],[170],642⟩,⟨160,(7),[1,2,5,6,13,14],[170],641⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3008
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3009
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3010
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3011
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3012
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3013
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3014
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3015
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3016
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3017
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3018
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3019
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3020
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3021
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3022
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3023
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3024
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3025
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3026
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3027
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3028
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3029
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3030
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3031
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3032
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3033
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3034
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3035
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3036
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3037
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3038
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3039
end Section14Records_1_3008_3040

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3008_3040


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3040_3072
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_3040_3072
private theorem valid3040 : RecordDataValid section14Catalog 1 (⟨160,(8),[1,2,5,6,13,14],[170],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3041 : RecordDataValid section14Catalog 1 (⟨160,(9),[1,2,5,6,13,14],[170],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3042 : RecordDataValid section14Catalog 1 (⟨160,(10),[1,2,5,6,13,14],[170],640⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨640,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],641⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3043 : RecordDataValid section14Catalog 1 (⟨160,(11),[1,2,5,6,13,14],[170],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3044 : RecordDataValid section14Catalog 1 (⟨160,(12),[1,2,5,6,13,14],[170],638⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3045 : RecordDataValid section14Catalog 1 (⟨160,(13),[1,2,5,6,13,14],[170],639⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3046 : RecordDataValid section14Catalog 1 (⟨160,(14),[1,2,5,6,13,14],[170],643⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨643,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],644⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3047 : RecordDataValid section14Catalog 1 (⟨160,(15),[1,2,5,6,13,14],[170],641⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨641,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],642⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3048 : RecordDataValid section14Catalog 1 (⟨163,(0),[1,2,5,6,13,14],[170],406⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨406,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],407⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3049 : RecordDataValid section14Catalog 1 (⟨163,(1),[1,2,5,6,13,14],[170],407⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨407,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],408⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3050 : RecordDataValid section14Catalog 1 (⟨163,(2),[1,2,5,6,13,14],[170],406⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨406,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],407⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3051 : RecordDataValid section14Catalog 1 (⟨163,(3),[1,2,5,6,13,14],[170],408⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨408,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],409⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3052 : RecordDataValid section14Catalog 1 (⟨163,(4),[1,2,5,6,13,14],[170],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3053 : RecordDataValid section14Catalog 1 (⟨163,(5),[1,2,5,6,13,14],[170],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3054 : RecordDataValid section14Catalog 1 (⟨163,(6),[1,2,5,6,13,14],[170],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3055 : RecordDataValid section14Catalog 1 (⟨163,(7),[1,2,5,6,13,14],[170],409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3056 : RecordDataValid section14Catalog 1 (⟨163,(8),[1,2,5,6,13,14],[170],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3057 : RecordDataValid section14Catalog 1 (⟨163,(9),[1,2,5,6,13,14],[170],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3058 : RecordDataValid section14Catalog 1 (⟨163,(10),[1,2,5,6,13,14],[170],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3059 : RecordDataValid section14Catalog 1 (⟨163,(11),[1,2,5,6,13,14],[170],410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3060 : RecordDataValid section14Catalog 1 (⟨163,(12),[1,2,5,6,13,14],[170],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3061 : RecordDataValid section14Catalog 1 (⟨163,(13),[1,2,5,6,13,14],[170],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3062 : RecordDataValid section14Catalog 1 (⟨163,(14),[1,2,5,6,13,14],[170],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3063 : RecordDataValid section14Catalog 1 (⟨163,(15),[1,2,5,6,13,14],[170],411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3064 : RecordDataValid section14Catalog 1 (⟨166,(0),[1,2,5,6,13,14],[170],644⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨644,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],645⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3065 : RecordDataValid section14Catalog 1 (⟨166,(1),[1,2,5,6,13,14],[170],644⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨644,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],645⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3066 : RecordDataValid section14Catalog 1 (⟨166,(2),[1,2,5,6,13,14],[170],644⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨644,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],645⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3067 : RecordDataValid section14Catalog 1 (⟨166,(3),[1,2,5,6,13,14],[170],644⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨644,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],645⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3068 : RecordDataValid section14Catalog 1 (⟨166,(4),[1,2,5,6,13,14],[170],645⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨645,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],646⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3069 : RecordDataValid section14Catalog 1 (⟨166,(5),[1,2,5,6,13,14],[170],645⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨645,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],646⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3070 : RecordDataValid section14Catalog 1 (⟨166,(6),[1,2,5,6,13,14],[170],645⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨645,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],646⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3071 : RecordDataValid section14Catalog 1 (⟨166,(7),[1,2,5,6,13,14],[170],645⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨645,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],646⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_3040_3072 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3040).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3040).take 32 = [⟨160,(8),[1,2,5,6,13,14],[170],638⟩,⟨160,(9),[1,2,5,6,13,14],[170],639⟩,⟨160,(10),[1,2,5,6,13,14],[170],640⟩,⟨160,(11),[1,2,5,6,13,14],[170],641⟩,⟨160,(12),[1,2,5,6,13,14],[170],638⟩,⟨160,(13),[1,2,5,6,13,14],[170],639⟩,⟨160,(14),[1,2,5,6,13,14],[170],643⟩,⟨160,(15),[1,2,5,6,13,14],[170],641⟩,⟨163,(0),[1,2,5,6,13,14],[170],406⟩,⟨163,(1),[1,2,5,6,13,14],[170],407⟩,⟨163,(2),[1,2,5,6,13,14],[170],406⟩,⟨163,(3),[1,2,5,6,13,14],[170],408⟩,⟨163,(4),[1,2,5,6,13,14],[170],409⟩,⟨163,(5),[1,2,5,6,13,14],[170],409⟩,⟨163,(6),[1,2,5,6,13,14],[170],409⟩,⟨163,(7),[1,2,5,6,13,14],[170],409⟩,⟨163,(8),[1,2,5,6,13,14],[170],410⟩,⟨163,(9),[1,2,5,6,13,14],[170],410⟩,⟨163,(10),[1,2,5,6,13,14],[170],410⟩,⟨163,(11),[1,2,5,6,13,14],[170],410⟩,⟨163,(12),[1,2,5,6,13,14],[170],411⟩,⟨163,(13),[1,2,5,6,13,14],[170],411⟩,⟨163,(14),[1,2,5,6,13,14],[170],411⟩,⟨163,(15),[1,2,5,6,13,14],[170],411⟩,⟨166,(0),[1,2,5,6,13,14],[170],644⟩,⟨166,(1),[1,2,5,6,13,14],[170],644⟩,⟨166,(2),[1,2,5,6,13,14],[170],644⟩,⟨166,(3),[1,2,5,6,13,14],[170],644⟩,⟨166,(4),[1,2,5,6,13,14],[170],645⟩,⟨166,(5),[1,2,5,6,13,14],[170],645⟩,⟨166,(6),[1,2,5,6,13,14],[170],645⟩,⟨166,(7),[1,2,5,6,13,14],[170],645⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3040
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3041
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3042
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3043
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3044
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3045
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3046
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3047
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3048
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3049
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3050
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3051
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3052
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3053
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3054
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3055
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3056
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3057
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3058
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3059
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3060
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3061
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3062
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3063
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3064
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3065
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3066
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3067
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3068
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3069
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3070
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3071
end Section14Records_1_3040_3072

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3040_3072


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3072_3104
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_3072_3104
private theorem valid3072 : RecordDataValid section14Catalog 1 (⟨166,(8),[1,2,5,6,13,14],[170],646⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨646,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],647⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3073 : RecordDataValid section14Catalog 1 (⟨166,(9),[1,2,5,6,13,14],[170],647⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨647,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],648⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3074 : RecordDataValid section14Catalog 1 (⟨166,(10),[1,2,5,6,13,14],[170],646⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨646,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],647⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3075 : RecordDataValid section14Catalog 1 (⟨166,(11),[1,2,5,6,13,14],[170],648⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨648,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],649⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3076 : RecordDataValid section14Catalog 1 (⟨166,(12),[1,2,5,6,13,14],[170],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3077 : RecordDataValid section14Catalog 1 (⟨166,(13),[1,2,5,6,13,14],[170],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3078 : RecordDataValid section14Catalog 1 (⟨166,(14),[1,2,5,6,13,14],[170],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3079 : RecordDataValid section14Catalog 1 (⟨166,(15),[1,2,5,6,13,14],[170],649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨649,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],650⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3080 : RecordDataValid section14Catalog 1 (⟨167,(0),[1,2,5,6,13,14],[170],418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨418,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],419⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3081 : RecordDataValid section14Catalog 1 (⟨167,(1),[1,2,5,6,13,14],[170],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3082 : RecordDataValid section14Catalog 1 (⟨167,(2),[1,2,5,6,13,14],[170],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3083 : RecordDataValid section14Catalog 1 (⟨167,(3),[1,2,5,6,13,14],[170],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3084 : RecordDataValid section14Catalog 1 (⟨167,(4),[1,2,5,6,13,14],[170],422⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨422,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],423⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3085 : RecordDataValid section14Catalog 1 (⟨167,(5),[1,2,5,6,13,14],[170],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3086 : RecordDataValid section14Catalog 1 (⟨167,(6),[1,2,5,6,13,14],[170],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3087 : RecordDataValid section14Catalog 1 (⟨167,(7),[1,2,5,6,13,14],[170],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3088 : RecordDataValid section14Catalog 1 (⟨167,(8),[1,2,5,6,13,14],[170],418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨418,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],419⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3089 : RecordDataValid section14Catalog 1 (⟨167,(9),[1,2,5,6,13,14],[170],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3090 : RecordDataValid section14Catalog 1 (⟨167,(10),[1,2,5,6,13,14],[170],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3091 : RecordDataValid section14Catalog 1 (⟨167,(11),[1,2,5,6,13,14],[170],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3092 : RecordDataValid section14Catalog 1 (⟨167,(12),[1,2,5,6,13,14],[170],423⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨423,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],424⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3093 : RecordDataValid section14Catalog 1 (⟨167,(13),[1,2,5,6,13,14],[170],419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3094 : RecordDataValid section14Catalog 1 (⟨167,(14),[1,2,5,6,13,14],[170],420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3095 : RecordDataValid section14Catalog 1 (⟨167,(15),[1,2,5,6,13,14],[170],421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3096 : RecordDataValid section14Catalog 1 (⟨171,(0),[1,2,5,6,13,14],[170],650⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨650,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],651⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3097 : RecordDataValid section14Catalog 1 (⟨171,(1),[1,2,5,6,13,14],[170],651⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨651,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],652⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3098 : RecordDataValid section14Catalog 1 (⟨171,(2),[1,2,5,6,13,14],[170],652⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨652,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],653⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3099 : RecordDataValid section14Catalog 1 (⟨171,(3),[1,2,5,6,13,14],[170],653⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨653,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],654⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3100 : RecordDataValid section14Catalog 1 (⟨172,(0),[1,2,5,6,13,14],[170],428⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨428,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],429⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3101 : RecordDataValid section14Catalog 1 (⟨172,(1),[1,2,5,6,13,14],[170],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3102 : RecordDataValid section14Catalog 1 (⟨172,(2),[1,2,5,6,13,14],[170],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3103 : RecordDataValid section14Catalog 1 (⟨172,(3),[1,2,5,6,13,14],[170],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_3072_3104 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3072).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3072).take 32 = [⟨166,(8),[1,2,5,6,13,14],[170],646⟩,⟨166,(9),[1,2,5,6,13,14],[170],647⟩,⟨166,(10),[1,2,5,6,13,14],[170],646⟩,⟨166,(11),[1,2,5,6,13,14],[170],648⟩,⟨166,(12),[1,2,5,6,13,14],[170],649⟩,⟨166,(13),[1,2,5,6,13,14],[170],649⟩,⟨166,(14),[1,2,5,6,13,14],[170],649⟩,⟨166,(15),[1,2,5,6,13,14],[170],649⟩,⟨167,(0),[1,2,5,6,13,14],[170],418⟩,⟨167,(1),[1,2,5,6,13,14],[170],419⟩,⟨167,(2),[1,2,5,6,13,14],[170],420⟩,⟨167,(3),[1,2,5,6,13,14],[170],421⟩,⟨167,(4),[1,2,5,6,13,14],[170],422⟩,⟨167,(5),[1,2,5,6,13,14],[170],419⟩,⟨167,(6),[1,2,5,6,13,14],[170],420⟩,⟨167,(7),[1,2,5,6,13,14],[170],421⟩,⟨167,(8),[1,2,5,6,13,14],[170],418⟩,⟨167,(9),[1,2,5,6,13,14],[170],419⟩,⟨167,(10),[1,2,5,6,13,14],[170],420⟩,⟨167,(11),[1,2,5,6,13,14],[170],421⟩,⟨167,(12),[1,2,5,6,13,14],[170],423⟩,⟨167,(13),[1,2,5,6,13,14],[170],419⟩,⟨167,(14),[1,2,5,6,13,14],[170],420⟩,⟨167,(15),[1,2,5,6,13,14],[170],421⟩,⟨171,(0),[1,2,5,6,13,14],[170],650⟩,⟨171,(1),[1,2,5,6,13,14],[170],651⟩,⟨171,(2),[1,2,5,6,13,14],[170],652⟩,⟨171,(3),[1,2,5,6,13,14],[170],653⟩,⟨172,(0),[1,2,5,6,13,14],[170],428⟩,⟨172,(1),[1,2,5,6,13,14],[170],429⟩,⟨172,(2),[1,2,5,6,13,14],[170],430⟩,⟨172,(3),[1,2,5,6,13,14],[170],431⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3072
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3073
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3074
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3075
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3076
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3077
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3078
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3079
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3080
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3081
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3082
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3083
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3084
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3085
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3086
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3087
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3088
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3089
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3090
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3091
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3092
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3093
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3094
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3095
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3096
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3097
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3098
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3099
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3100
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3101
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3102
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3103
end Section14Records_1_3072_3104

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3072_3104


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3104_3136
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_3104_3136
private theorem valid3104 : RecordDataValid section14Catalog 1 (⟨172,(4),[1,2,5,6,13,14],[170],432⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨432,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],433⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3105 : RecordDataValid section14Catalog 1 (⟨172,(5),[1,2,5,6,13,14],[170],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3106 : RecordDataValid section14Catalog 1 (⟨172,(6),[1,2,5,6,13,14],[170],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3107 : RecordDataValid section14Catalog 1 (⟨172,(7),[1,2,5,6,13,14],[170],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3108 : RecordDataValid section14Catalog 1 (⟨172,(8),[1,2,5,6,13,14],[170],428⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨428,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],429⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3109 : RecordDataValid section14Catalog 1 (⟨172,(9),[1,2,5,6,13,14],[170],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3110 : RecordDataValid section14Catalog 1 (⟨172,(10),[1,2,5,6,13,14],[170],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3111 : RecordDataValid section14Catalog 1 (⟨172,(11),[1,2,5,6,13,14],[170],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3112 : RecordDataValid section14Catalog 1 (⟨172,(12),[1,2,5,6,13,14],[170],433⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨433,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],434⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3113 : RecordDataValid section14Catalog 1 (⟨172,(13),[1,2,5,6,13,14],[170],429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3114 : RecordDataValid section14Catalog 1 (⟨172,(14),[1,2,5,6,13,14],[170],430⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3115 : RecordDataValid section14Catalog 1 (⟨172,(15),[1,2,5,6,13,14],[170],431⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3116 : RecordDataValid section14Catalog 1 (⟨175,(0),[1,2,5,6,13,14],[170],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3117 : RecordDataValid section14Catalog 1 (⟨175,(1),[1,2,5,6,13,14],[170],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3118 : RecordDataValid section14Catalog 1 (⟨175,(2),[1,2,5,6,13,14],[170],656⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨656,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],657⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3119 : RecordDataValid section14Catalog 1 (⟨175,(3),[1,2,5,6,13,14],[170],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3120 : RecordDataValid section14Catalog 1 (⟨175,(4),[1,2,5,6,13,14],[170],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3121 : RecordDataValid section14Catalog 1 (⟨175,(5),[1,2,5,6,13,14],[170],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3122 : RecordDataValid section14Catalog 1 (⟨175,(6),[1,2,5,6,13,14],[170],658⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨658,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],659⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3123 : RecordDataValid section14Catalog 1 (⟨175,(7),[1,2,5,6,13,14],[170],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3124 : RecordDataValid section14Catalog 1 (⟨175,(8),[1,2,5,6,13,14],[170],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3125 : RecordDataValid section14Catalog 1 (⟨175,(9),[1,2,5,6,13,14],[170],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3126 : RecordDataValid section14Catalog 1 (⟨175,(10),[1,2,5,6,13,14],[170],656⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨656,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],657⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3127 : RecordDataValid section14Catalog 1 (⟨175,(11),[1,2,5,6,13,14],[170],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3128 : RecordDataValid section14Catalog 1 (⟨175,(12),[1,2,5,6,13,14],[170],654⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨654,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3129 : RecordDataValid section14Catalog 1 (⟨175,(13),[1,2,5,6,13,14],[170],655⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨655,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],656⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3130 : RecordDataValid section14Catalog 1 (⟨175,(14),[1,2,5,6,13,14],[170],659⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨659,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],660⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3131 : RecordDataValid section14Catalog 1 (⟨175,(15),[1,2,5,6,13,14],[170],657⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨657,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],658⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3132 : RecordDataValid section14Catalog 1 (⟨178,(0),[1,2,5,6,13,14],[170],660⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨660,[1,2,3,5,6,7,10,11,13,14,15],661⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3133 : RecordDataValid section14Catalog 1 (⟨178,(1),[1,2,5,6,13,14],[170],661⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨661,[1,2,3,5,6,7,10,11,13,14,15],662⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3134 : RecordDataValid section14Catalog 1 (⟨178,(2),[1,2,5,6,13,14],[170],660⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨660,[1,2,3,5,6,7,10,11,13,14,15],661⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3135 : RecordDataValid section14Catalog 1 (⟨178,(3),[1,2,5,6,13,14],[170],662⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨662,[1,2,3,5,6,7,10,11,13,14,15],663⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_3104_3136 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3104).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3104).take 32 = [⟨172,(4),[1,2,5,6,13,14],[170],432⟩,⟨172,(5),[1,2,5,6,13,14],[170],429⟩,⟨172,(6),[1,2,5,6,13,14],[170],430⟩,⟨172,(7),[1,2,5,6,13,14],[170],431⟩,⟨172,(8),[1,2,5,6,13,14],[170],428⟩,⟨172,(9),[1,2,5,6,13,14],[170],429⟩,⟨172,(10),[1,2,5,6,13,14],[170],430⟩,⟨172,(11),[1,2,5,6,13,14],[170],431⟩,⟨172,(12),[1,2,5,6,13,14],[170],433⟩,⟨172,(13),[1,2,5,6,13,14],[170],429⟩,⟨172,(14),[1,2,5,6,13,14],[170],430⟩,⟨172,(15),[1,2,5,6,13,14],[170],431⟩,⟨175,(0),[1,2,5,6,13,14],[170],654⟩,⟨175,(1),[1,2,5,6,13,14],[170],655⟩,⟨175,(2),[1,2,5,6,13,14],[170],656⟩,⟨175,(3),[1,2,5,6,13,14],[170],657⟩,⟨175,(4),[1,2,5,6,13,14],[170],654⟩,⟨175,(5),[1,2,5,6,13,14],[170],655⟩,⟨175,(6),[1,2,5,6,13,14],[170],658⟩,⟨175,(7),[1,2,5,6,13,14],[170],657⟩,⟨175,(8),[1,2,5,6,13,14],[170],654⟩,⟨175,(9),[1,2,5,6,13,14],[170],655⟩,⟨175,(10),[1,2,5,6,13,14],[170],656⟩,⟨175,(11),[1,2,5,6,13,14],[170],657⟩,⟨175,(12),[1,2,5,6,13,14],[170],654⟩,⟨175,(13),[1,2,5,6,13,14],[170],655⟩,⟨175,(14),[1,2,5,6,13,14],[170],659⟩,⟨175,(15),[1,2,5,6,13,14],[170],657⟩,⟨178,(0),[1,2,5,6,13,14],[170],660⟩,⟨178,(1),[1,2,5,6,13,14],[170],661⟩,⟨178,(2),[1,2,5,6,13,14],[170],660⟩,⟨178,(3),[1,2,5,6,13,14],[170],662⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3104
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3105
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3106
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3107
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3108
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3109
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3110
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3111
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3112
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3113
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3114
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3115
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3116
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3117
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3118
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3119
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3120
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3121
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3122
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3123
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3124
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3125
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3126
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3127
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3128
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3129
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3130
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3131
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3132
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3133
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3134
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3135
end Section14Records_1_3104_3136

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3104_3136

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3008).take 128, section14RecordValid section14Catalog 1 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (1 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 1 r
  exact (all_of_interval_split P xs 3008 3072 3136 (by decide) (by decide) (all_of_interval_split P xs 3008 3040 3072 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_3008_3040 hnum) (Freiman.workReverse20260919_s0001_records_3040_3072 hnum)) (all_of_interval_split P xs 3072 3104 3136 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_3072_3104 hnum) (Freiman.workReverse20260919_s0001_records_3104_3136 hnum)))

#print axioms solution
