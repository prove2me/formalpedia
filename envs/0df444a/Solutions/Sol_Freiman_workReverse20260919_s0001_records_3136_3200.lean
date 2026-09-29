-- Prove2me | solution 1 for Freiman.workReverse20260919_s0001_records_3136_3200
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T02:47:48.152985+00:00
-- url     : https://prove2.me/submissions/c2813afe-2688-41fd-9fef-3c2140507ebd

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3136_3168
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_3136_3168
private theorem valid3136 : RecordDataValid section14Catalog 1 (⟨178,(4),[1,2,5,6,13,14],[170],663⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨663,[1,2,3,5,6,7,10,11,13,14,15],664⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3137 : RecordDataValid section14Catalog 1 (⟨178,(5),[1,2,5,6,13,14],[170],663⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨663,[1,2,3,5,6,7,10,11,13,14,15],664⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3138 : RecordDataValid section14Catalog 1 (⟨178,(6),[1,2,5,6,13,14],[170],663⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨663,[1,2,3,5,6,7,10,11,13,14,15],664⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3139 : RecordDataValid section14Catalog 1 (⟨178,(7),[1,2,5,6,13,14],[170],663⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨663,[1,2,3,5,6,7,10,11,13,14,15],664⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3140 : RecordDataValid section14Catalog 1 (⟨178,(8),[1,2,5,6,13,14],[170],664⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨664,[1,2,3,5,6,7,10,11,13,14,15],665⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3141 : RecordDataValid section14Catalog 1 (⟨178,(9),[1,2,5,6,13,14],[170],664⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨664,[1,2,3,5,6,7,10,11,13,14,15],665⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3142 : RecordDataValid section14Catalog 1 (⟨178,(10),[1,2,5,6,13,14],[170],664⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨664,[1,2,3,5,6,7,10,11,13,14,15],665⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3143 : RecordDataValid section14Catalog 1 (⟨178,(11),[1,2,5,6,13,14],[170],664⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨664,[1,2,3,5,6,7,10,11,13,14,15],665⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3144 : RecordDataValid section14Catalog 1 (⟨178,(12),[1,2,5,6,13,14],[170],665⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨665,[1,2,3,5,6,7,10,11,13,14,15],666⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3145 : RecordDataValid section14Catalog 1 (⟨178,(13),[1,2,5,6,13,14],[170],665⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨665,[1,2,3,5,6,7,10,11,13,14,15],666⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3146 : RecordDataValid section14Catalog 1 (⟨178,(14),[1,2,5,6,13,14],[170],665⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨665,[1,2,3,5,6,7,10,11,13,14,15],666⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3147 : RecordDataValid section14Catalog 1 (⟨178,(15),[1,2,5,6,13,14],[170],665⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨665,[1,2,3,5,6,7,10,11,13,14,15],666⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3148 : RecordDataValid section14Catalog 1 (⟨180,(0),[1,2,5,6,13,14],[170],666⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨666,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],667⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3149 : RecordDataValid section14Catalog 1 (⟨180,(1),[1,2,5,6,13,14],[170],667⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨667,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],668⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3150 : RecordDataValid section14Catalog 1 (⟨180,(2),[1,2,5,6,13,14],[170],668⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨668,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],669⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3151 : RecordDataValid section14Catalog 1 (⟨180,(3),[1,2,5,6,13,14],[170],669⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨669,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],670⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3152 : RecordDataValid section14Catalog 1 (⟨180,(4),[1,2,5,6,13,14],[170],666⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨666,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],667⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3153 : RecordDataValid section14Catalog 1 (⟨180,(5),[1,2,5,6,13,14],[170],667⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨667,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],668⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3154 : RecordDataValid section14Catalog 1 (⟨180,(6),[1,2,5,6,13,14],[170],670⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨670,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],671⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3155 : RecordDataValid section14Catalog 1 (⟨180,(7),[1,2,5,6,13,14],[170],669⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨669,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],670⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3156 : RecordDataValid section14Catalog 1 (⟨180,(8),[1,2,5,6,13,14],[170],666⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨666,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],667⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3157 : RecordDataValid section14Catalog 1 (⟨180,(9),[1,2,5,6,13,14],[170],667⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨667,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],668⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3158 : RecordDataValid section14Catalog 1 (⟨180,(10),[1,2,5,6,13,14],[170],668⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨668,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],669⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3159 : RecordDataValid section14Catalog 1 (⟨180,(11),[1,2,5,6,13,14],[170],669⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨669,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],670⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3160 : RecordDataValid section14Catalog 1 (⟨180,(12),[1,2,5,6,13,14],[170],666⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨666,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],667⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3161 : RecordDataValid section14Catalog 1 (⟨180,(13),[1,2,5,6,13,14],[170],667⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨667,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],668⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3162 : RecordDataValid section14Catalog 1 (⟨180,(14),[1,2,5,6,13,14],[170],671⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨671,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],672⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3163 : RecordDataValid section14Catalog 1 (⟨180,(15),[1,2,5,6,13,14],[170],669⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨669,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],670⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3164 : RecordDataValid section14Catalog 1 (⟨183,(0),[1,2,5,6,13,14],[170],672⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨672,[1,2,3,5,6,7,10,11,13,14,15],673⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3165 : RecordDataValid section14Catalog 1 (⟨183,(1),[1,2,5,6,13,14],[170],673⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨673,[1,2,3,5,6,7,10,11,13,14,15],674⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3166 : RecordDataValid section14Catalog 1 (⟨183,(2),[1,2,5,6,13,14],[170],672⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨672,[1,2,3,5,6,7,10,11,13,14,15],673⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3167 : RecordDataValid section14Catalog 1 (⟨183,(3),[1,2,5,6,13,14],[170],674⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨674,[1,2,3,5,6,7,10,11,13,14,15],675⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_3136_3168 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3136).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3136).take 32 = [⟨178,(4),[1,2,5,6,13,14],[170],663⟩,⟨178,(5),[1,2,5,6,13,14],[170],663⟩,⟨178,(6),[1,2,5,6,13,14],[170],663⟩,⟨178,(7),[1,2,5,6,13,14],[170],663⟩,⟨178,(8),[1,2,5,6,13,14],[170],664⟩,⟨178,(9),[1,2,5,6,13,14],[170],664⟩,⟨178,(10),[1,2,5,6,13,14],[170],664⟩,⟨178,(11),[1,2,5,6,13,14],[170],664⟩,⟨178,(12),[1,2,5,6,13,14],[170],665⟩,⟨178,(13),[1,2,5,6,13,14],[170],665⟩,⟨178,(14),[1,2,5,6,13,14],[170],665⟩,⟨178,(15),[1,2,5,6,13,14],[170],665⟩,⟨180,(0),[1,2,5,6,13,14],[170],666⟩,⟨180,(1),[1,2,5,6,13,14],[170],667⟩,⟨180,(2),[1,2,5,6,13,14],[170],668⟩,⟨180,(3),[1,2,5,6,13,14],[170],669⟩,⟨180,(4),[1,2,5,6,13,14],[170],666⟩,⟨180,(5),[1,2,5,6,13,14],[170],667⟩,⟨180,(6),[1,2,5,6,13,14],[170],670⟩,⟨180,(7),[1,2,5,6,13,14],[170],669⟩,⟨180,(8),[1,2,5,6,13,14],[170],666⟩,⟨180,(9),[1,2,5,6,13,14],[170],667⟩,⟨180,(10),[1,2,5,6,13,14],[170],668⟩,⟨180,(11),[1,2,5,6,13,14],[170],669⟩,⟨180,(12),[1,2,5,6,13,14],[170],666⟩,⟨180,(13),[1,2,5,6,13,14],[170],667⟩,⟨180,(14),[1,2,5,6,13,14],[170],671⟩,⟨180,(15),[1,2,5,6,13,14],[170],669⟩,⟨183,(0),[1,2,5,6,13,14],[170],672⟩,⟨183,(1),[1,2,5,6,13,14],[170],673⟩,⟨183,(2),[1,2,5,6,13,14],[170],672⟩,⟨183,(3),[1,2,5,6,13,14],[170],674⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3136
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3137
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3138
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3139
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3140
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3141
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3142
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3143
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3144
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3145
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3146
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3147
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3148
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3149
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3150
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3151
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3152
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3153
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3154
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3155
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3156
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3157
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3158
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3159
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3160
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3161
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3162
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3163
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3164
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3165
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3166
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3167
end Section14Records_1_3136_3168

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3136_3168


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3168_3200
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_3168_3200
private theorem valid3168 : RecordDataValid section14Catalog 1 (⟨183,(4),[1,2,5,6,13,14],[170],675⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨675,[1,2,3,5,6,7,10,11,13,14,15],676⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3169 : RecordDataValid section14Catalog 1 (⟨183,(5),[1,2,5,6,13,14],[170],675⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨675,[1,2,3,5,6,7,10,11,13,14,15],676⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3170 : RecordDataValid section14Catalog 1 (⟨183,(6),[1,2,5,6,13,14],[170],675⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨675,[1,2,3,5,6,7,10,11,13,14,15],676⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3171 : RecordDataValid section14Catalog 1 (⟨183,(7),[1,2,5,6,13,14],[170],675⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨675,[1,2,3,5,6,7,10,11,13,14,15],676⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3172 : RecordDataValid section14Catalog 1 (⟨183,(8),[1,2,5,6,13,14],[170],676⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨676,[1,2,3,5,6,7,10,11,13,14,15],677⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3173 : RecordDataValid section14Catalog 1 (⟨183,(9),[1,2,5,6,13,14],[170],676⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨676,[1,2,3,5,6,7,10,11,13,14,15],677⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3174 : RecordDataValid section14Catalog 1 (⟨183,(10),[1,2,5,6,13,14],[170],676⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨676,[1,2,3,5,6,7,10,11,13,14,15],677⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3175 : RecordDataValid section14Catalog 1 (⟨183,(11),[1,2,5,6,13,14],[170],676⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨676,[1,2,3,5,6,7,10,11,13,14,15],677⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3176 : RecordDataValid section14Catalog 1 (⟨183,(12),[1,2,5,6,13,14],[170],677⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨677,[1,2,3,5,6,7,10,11,13,14,15],678⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3177 : RecordDataValid section14Catalog 1 (⟨183,(13),[1,2,5,6,13,14],[170],677⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨677,[1,2,3,5,6,7,10,11,13,14,15],678⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3178 : RecordDataValid section14Catalog 1 (⟨183,(14),[1,2,5,6,13,14],[170],677⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨677,[1,2,3,5,6,7,10,11,13,14,15],678⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3179 : RecordDataValid section14Catalog 1 (⟨183,(15),[1,2,5,6,13,14],[170],677⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨677,[1,2,3,5,6,7,10,11,13,14,15],678⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3180 : RecordDataValid section14Catalog 1 (⟨185,(0),[1,2,5,6,13,14],[170],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3181 : RecordDataValid section14Catalog 1 (⟨185,(1),[1,2,5,6,13,14],[170],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3182 : RecordDataValid section14Catalog 1 (⟨185,(2),[1,2,5,6,13,14],[170],680⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨680,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],681⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3183 : RecordDataValid section14Catalog 1 (⟨185,(3),[1,2,5,6,13,14],[170],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3184 : RecordDataValid section14Catalog 1 (⟨185,(4),[1,2,5,6,13,14],[170],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3185 : RecordDataValid section14Catalog 1 (⟨185,(5),[1,2,5,6,13,14],[170],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3186 : RecordDataValid section14Catalog 1 (⟨185,(6),[1,2,5,6,13,14],[170],682⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨682,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],683⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3187 : RecordDataValid section14Catalog 1 (⟨185,(7),[1,2,5,6,13,14],[170],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3188 : RecordDataValid section14Catalog 1 (⟨185,(8),[1,2,5,6,13,14],[170],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3189 : RecordDataValid section14Catalog 1 (⟨185,(9),[1,2,5,6,13,14],[170],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3190 : RecordDataValid section14Catalog 1 (⟨185,(10),[1,2,5,6,13,14],[170],680⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨680,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],681⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3191 : RecordDataValid section14Catalog 1 (⟨185,(11),[1,2,5,6,13,14],[170],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3192 : RecordDataValid section14Catalog 1 (⟨185,(12),[1,2,5,6,13,14],[170],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3193 : RecordDataValid section14Catalog 1 (⟨185,(13),[1,2,5,6,13,14],[170],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3194 : RecordDataValid section14Catalog 1 (⟨185,(14),[1,2,5,6,13,14],[170],683⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨683,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],684⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3195 : RecordDataValid section14Catalog 1 (⟨185,(15),[1,2,5,6,13,14],[170],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3196 : RecordDataValid section14Catalog 1 (⟨188,(0),[1,2,5,6,13,14],[170],684⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨684,[1,2,3,5,6,7,10,11,13,14,15],685⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3197 : RecordDataValid section14Catalog 1 (⟨188,(1),[1,2,5,6,13,14],[170],685⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨685,[1,2,3,5,6,7,10,11,13,14,15],686⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3198 : RecordDataValid section14Catalog 1 (⟨188,(2),[1,2,5,6,13,14],[170],684⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨684,[1,2,3,5,6,7,10,11,13,14,15],685⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3199 : RecordDataValid section14Catalog 1 (⟨188,(3),[1,2,5,6,13,14],[170],686⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨686,[1,2,3,5,6,7,10,11,13,14,15],687⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_3168_3200 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3168).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3168).take 32 = [⟨183,(4),[1,2,5,6,13,14],[170],675⟩,⟨183,(5),[1,2,5,6,13,14],[170],675⟩,⟨183,(6),[1,2,5,6,13,14],[170],675⟩,⟨183,(7),[1,2,5,6,13,14],[170],675⟩,⟨183,(8),[1,2,5,6,13,14],[170],676⟩,⟨183,(9),[1,2,5,6,13,14],[170],676⟩,⟨183,(10),[1,2,5,6,13,14],[170],676⟩,⟨183,(11),[1,2,5,6,13,14],[170],676⟩,⟨183,(12),[1,2,5,6,13,14],[170],677⟩,⟨183,(13),[1,2,5,6,13,14],[170],677⟩,⟨183,(14),[1,2,5,6,13,14],[170],677⟩,⟨183,(15),[1,2,5,6,13,14],[170],677⟩,⟨185,(0),[1,2,5,6,13,14],[170],678⟩,⟨185,(1),[1,2,5,6,13,14],[170],679⟩,⟨185,(2),[1,2,5,6,13,14],[170],680⟩,⟨185,(3),[1,2,5,6,13,14],[170],681⟩,⟨185,(4),[1,2,5,6,13,14],[170],678⟩,⟨185,(5),[1,2,5,6,13,14],[170],679⟩,⟨185,(6),[1,2,5,6,13,14],[170],682⟩,⟨185,(7),[1,2,5,6,13,14],[170],681⟩,⟨185,(8),[1,2,5,6,13,14],[170],678⟩,⟨185,(9),[1,2,5,6,13,14],[170],679⟩,⟨185,(10),[1,2,5,6,13,14],[170],680⟩,⟨185,(11),[1,2,5,6,13,14],[170],681⟩,⟨185,(12),[1,2,5,6,13,14],[170],678⟩,⟨185,(13),[1,2,5,6,13,14],[170],679⟩,⟨185,(14),[1,2,5,6,13,14],[170],683⟩,⟨185,(15),[1,2,5,6,13,14],[170],681⟩,⟨188,(0),[1,2,5,6,13,14],[170],684⟩,⟨188,(1),[1,2,5,6,13,14],[170],685⟩,⟨188,(2),[1,2,5,6,13,14],[170],684⟩,⟨188,(3),[1,2,5,6,13,14],[170],686⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3168
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3169
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3170
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3171
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3172
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3173
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3174
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3175
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3176
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3177
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3178
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3179
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3180
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3181
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3182
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3183
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3184
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3185
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3186
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3187
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3188
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3189
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3190
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3191
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3192
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3193
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3194
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3195
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3196
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3197
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3198
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3199
end Section14Records_1_3168_3200

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3168_3200

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3136).take 64, section14RecordValid section14Catalog 1 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (1 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 1 r
  exact (all_of_interval_split P xs 3136 3168 3200 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_3136_3168 hnum) (Freiman.workReverse20260919_s0001_records_3168_3200 hnum))

#print axioms solution
