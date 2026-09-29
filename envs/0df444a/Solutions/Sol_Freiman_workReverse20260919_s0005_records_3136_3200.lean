-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_3136_3200
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:30:24.368012+00:00
-- url     : https://prove2.me/submissions/c0fbafee-428f-458b-8eb2-b99854d3ffac

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3136_3168
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_3136_3168
private theorem valid3136 : RecordDataValid section14Catalog 5 (⟨200,(2),[1,2,5,6,13,14],[170],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3137 : RecordDataValid section14Catalog 5 (⟨200,(2),[5,6],[174],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3138 : RecordDataValid section14Catalog 5 (⟨200,(3),[1,2,5,6,13,14],[170],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3139 : RecordDataValid section14Catalog 5 (⟨200,(3),[5,6],[174],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3140 : RecordDataValid section14Catalog 5 (⟨200,(4),[1,2,5,6,13,14],[170],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3141 : RecordDataValid section14Catalog 5 (⟨200,(4),[5,6],[174],704⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3142 : RecordDataValid section14Catalog 5 (⟨200,(5),[1,2,5,6,13,14],[170],705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3143 : RecordDataValid section14Catalog 5 (⟨200,(5),[5,6],[174],705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3144 : RecordDataValid section14Catalog 5 (⟨200,(6),[1,2,5,6,13,14],[170],705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3145 : RecordDataValid section14Catalog 5 (⟨200,(6),[5,6],[174],705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3146 : RecordDataValid section14Catalog 5 (⟨200,(7),[1,2,5,6,13,14],[170],705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3147 : RecordDataValid section14Catalog 5 (⟨200,(7),[5,6],[174],705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3148 : RecordDataValid section14Catalog 5 (⟨200,(8),[1,2,5,6,13,14],[170],705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3149 : RecordDataValid section14Catalog 5 (⟨200,(8),[5,6],[174],705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3150 : RecordDataValid section14Catalog 5 (⟨200,(9),[1,2,5,6,13,14],[170],705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3151 : RecordDataValid section14Catalog 5 (⟨200,(9),[5,6],[174],705⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3152 : RecordDataValid section14Catalog 5 (⟨200,(10),[1,2,5,6,13,14],[170],706⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨706,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],707⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3153 : RecordDataValid section14Catalog 5 (⟨200,(10),[5,6],[174],706⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨706,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],707⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3154 : RecordDataValid section14Catalog 5 (⟨200,(11),[1,2,5,6,13,14],[170],707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨707,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3155 : RecordDataValid section14Catalog 5 (⟨200,(11),[5,6],[174],707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨707,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3156 : RecordDataValid section14Catalog 5 (⟨200,(12),[1,2,5,6,13,14],[170],708⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨708,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],709⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3157 : RecordDataValid section14Catalog 5 (⟨200,(12),[5,6],[174],708⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨708,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],709⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3158 : RecordDataValid section14Catalog 5 (⟨200,(13),[1,2,5,6,13,14],[170],707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨707,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3159 : RecordDataValid section14Catalog 5 (⟨200,(13),[5,6],[174],707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨707,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3160 : RecordDataValid section14Catalog 5 (⟨200,(14),[1,2,5,6,13,14],[170],709⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨709,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],710⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3161 : RecordDataValid section14Catalog 5 (⟨200,(14),[5,6],[174],709⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨709,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],710⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3162 : RecordDataValid section14Catalog 5 (⟨200,(15),[1,2,5,6,13,14],[170],706⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨706,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],707⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3163 : RecordDataValid section14Catalog 5 (⟨200,(15),[5,6],[174],706⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨706,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],707⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3164 : RecordDataValid section14Catalog 5 (⟨200,(16),[1,2,5,6,13,14],[170],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3165 : RecordDataValid section14Catalog 5 (⟨200,(16),[5,6],[174],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3166 : RecordDataValid section14Catalog 5 (⟨200,(17),[1,2,5,6,13,14],[170],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3167 : RecordDataValid section14Catalog 5 (⟨200,(17),[5,6],[174],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_3136_3168 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3136).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3136).take 32 = [⟨200,(2),[1,2,5,6,13,14],[170],704⟩,⟨200,(2),[5,6],[174],704⟩,⟨200,(3),[1,2,5,6,13,14],[170],704⟩,⟨200,(3),[5,6],[174],704⟩,⟨200,(4),[1,2,5,6,13,14],[170],704⟩,⟨200,(4),[5,6],[174],704⟩,⟨200,(5),[1,2,5,6,13,14],[170],705⟩,⟨200,(5),[5,6],[174],705⟩,⟨200,(6),[1,2,5,6,13,14],[170],705⟩,⟨200,(6),[5,6],[174],705⟩,⟨200,(7),[1,2,5,6,13,14],[170],705⟩,⟨200,(7),[5,6],[174],705⟩,⟨200,(8),[1,2,5,6,13,14],[170],705⟩,⟨200,(8),[5,6],[174],705⟩,⟨200,(9),[1,2,5,6,13,14],[170],705⟩,⟨200,(9),[5,6],[174],705⟩,⟨200,(10),[1,2,5,6,13,14],[170],706⟩,⟨200,(10),[5,6],[174],706⟩,⟨200,(11),[1,2,5,6,13,14],[170],707⟩,⟨200,(11),[5,6],[174],707⟩,⟨200,(12),[1,2,5,6,13,14],[170],708⟩,⟨200,(12),[5,6],[174],708⟩,⟨200,(13),[1,2,5,6,13,14],[170],707⟩,⟨200,(13),[5,6],[174],707⟩,⟨200,(14),[1,2,5,6,13,14],[170],709⟩,⟨200,(14),[5,6],[174],709⟩,⟨200,(15),[1,2,5,6,13,14],[170],706⟩,⟨200,(15),[5,6],[174],706⟩,⟨200,(16),[1,2,5,6,13,14],[170],710⟩,⟨200,(16),[5,6],[174],710⟩,⟨200,(17),[1,2,5,6,13,14],[170],710⟩,⟨200,(17),[5,6],[174],710⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3136
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3137
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3138
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3139
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3140
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3141
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3142
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3143
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3144
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3145
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3146
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3147
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3148
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3149
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3150
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3151
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3152
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3153
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3154
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3155
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3156
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3157
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3158
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3159
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3160
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3161
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3162
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3163
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3164
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3165
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3166
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3167
end Section14Records_5_3136_3168

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3136_3168


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3168_3200
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_3168_3200
private theorem valid3168 : RecordDataValid section14Catalog 5 (⟨200,(18),[1,2,5,6,13,14],[170],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3169 : RecordDataValid section14Catalog 5 (⟨200,(18),[5,6],[174],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3170 : RecordDataValid section14Catalog 5 (⟨200,(19),[1,2,5,6,13,14],[170],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3171 : RecordDataValid section14Catalog 5 (⟨200,(19),[5,6],[174],710⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3172 : RecordDataValid section14Catalog 5 (⟨200,(20),[1,2,5,6,13,14],[170],706⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨706,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],707⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3173 : RecordDataValid section14Catalog 5 (⟨200,(20),[5,6],[174],706⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨706,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],707⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3174 : RecordDataValid section14Catalog 5 (⟨200,(21),[1,2,5,6,13,14],[170],707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨707,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3175 : RecordDataValid section14Catalog 5 (⟨200,(21),[5,6],[174],707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨707,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3176 : RecordDataValid section14Catalog 5 (⟨200,(22),[1,2,5,6,13,14],[170],708⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨708,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],709⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3177 : RecordDataValid section14Catalog 5 (⟨200,(22),[5,6],[174],708⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨708,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],709⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3178 : RecordDataValid section14Catalog 5 (⟨200,(23),[1,2,5,6,13,14],[170],707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨707,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3179 : RecordDataValid section14Catalog 5 (⟨200,(23),[5,6],[174],707⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨707,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],708⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3180 : RecordDataValid section14Catalog 5 (⟨200,(24),[1,2,5,6,13,14],[170],709⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨709,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],710⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3181 : RecordDataValid section14Catalog 5 (⟨200,(24),[5,6],[174],709⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨709,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],710⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3182 : RecordDataValid section14Catalog 5 (⟨202,(0),[1,2,5,6,13,14],[170],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3183 : RecordDataValid section14Catalog 5 (⟨202,(0),[5,6],[174],1015⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1015,[3,5,6,7],1019⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3184 : RecordDataValid section14Catalog 5 (⟨202,(1),[1,2,5,6,13,14],[170],468⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨468,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3185 : RecordDataValid section14Catalog 5 (⟨202,(1),[5,6],[174],1016⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1016,[3,5,6,7],1020⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3186 : RecordDataValid section14Catalog 5 (⟨202,(2),[1,2,5,6,13,14],[170],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3187 : RecordDataValid section14Catalog 5 (⟨202,(2),[5,6],[174],1015⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1015,[3,5,6,7],1019⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3188 : RecordDataValid section14Catalog 5 (⟨202,(3),[1,2,5,6,13,14],[170],469⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨469,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],470⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3189 : RecordDataValid section14Catalog 5 (⟨202,(3),[5,6],[174],1017⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1017,[3,5,6,7],1021⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3190 : RecordDataValid section14Catalog 5 (⟨202,(4),[1,2,5,6,13,14],[170],470⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨470,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3191 : RecordDataValid section14Catalog 5 (⟨202,(4),[5,6],[174],1018⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1018,[3,5,6,7],1022⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3192 : RecordDataValid section14Catalog 5 (⟨202,(5),[1,2,5,6,13,14],[170],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3193 : RecordDataValid section14Catalog 5 (⟨202,(5),[5,6],[174],1015⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1015,[3,5,6,7],1019⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3194 : RecordDataValid section14Catalog 5 (⟨202,(6),[1,2,5,6,13,14],[170],468⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨468,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3195 : RecordDataValid section14Catalog 5 (⟨202,(6),[5,6],[174],1016⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1016,[3,5,6,7],1020⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3196 : RecordDataValid section14Catalog 5 (⟨202,(7),[1,2,5,6,13,14],[170],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3197 : RecordDataValid section14Catalog 5 (⟨202,(7),[5,6],[174],1015⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1015,[3,5,6,7],1019⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3198 : RecordDataValid section14Catalog 5 (⟨202,(8),[1,2,5,6,13,14],[170],469⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨469,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],470⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3199 : RecordDataValid section14Catalog 5 (⟨202,(8),[5,6],[174],1017⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1017,[3,5,6,7],1021⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_3168_3200 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3168).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3168).take 32 = [⟨200,(18),[1,2,5,6,13,14],[170],710⟩,⟨200,(18),[5,6],[174],710⟩,⟨200,(19),[1,2,5,6,13,14],[170],710⟩,⟨200,(19),[5,6],[174],710⟩,⟨200,(20),[1,2,5,6,13,14],[170],706⟩,⟨200,(20),[5,6],[174],706⟩,⟨200,(21),[1,2,5,6,13,14],[170],707⟩,⟨200,(21),[5,6],[174],707⟩,⟨200,(22),[1,2,5,6,13,14],[170],708⟩,⟨200,(22),[5,6],[174],708⟩,⟨200,(23),[1,2,5,6,13,14],[170],707⟩,⟨200,(23),[5,6],[174],707⟩,⟨200,(24),[1,2,5,6,13,14],[170],709⟩,⟨200,(24),[5,6],[174],709⟩,⟨202,(0),[1,2,5,6,13,14],[170],467⟩,⟨202,(0),[5,6],[174],1015⟩,⟨202,(1),[1,2,5,6,13,14],[170],468⟩,⟨202,(1),[5,6],[174],1016⟩,⟨202,(2),[1,2,5,6,13,14],[170],467⟩,⟨202,(2),[5,6],[174],1015⟩,⟨202,(3),[1,2,5,6,13,14],[170],469⟩,⟨202,(3),[5,6],[174],1017⟩,⟨202,(4),[1,2,5,6,13,14],[170],470⟩,⟨202,(4),[5,6],[174],1018⟩,⟨202,(5),[1,2,5,6,13,14],[170],467⟩,⟨202,(5),[5,6],[174],1015⟩,⟨202,(6),[1,2,5,6,13,14],[170],468⟩,⟨202,(6),[5,6],[174],1016⟩,⟨202,(7),[1,2,5,6,13,14],[170],467⟩,⟨202,(7),[5,6],[174],1015⟩,⟨202,(8),[1,2,5,6,13,14],[170],469⟩,⟨202,(8),[5,6],[174],1017⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3168
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3169
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3170
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3171
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3172
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3173
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3174
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3175
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3176
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3177
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3178
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3179
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3180
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3181
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3182
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3183
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3184
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3185
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3186
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3187
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3188
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3189
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3190
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3191
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3192
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3193
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3194
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3195
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3196
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3197
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3198
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3199
end Section14Records_5_3168_3200

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_3168_3200

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3136).take 64, section14RecordValid section14Catalog 5 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (5 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 5 r
  exact (all_of_interval_split P xs 3136 3168 3200 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_3136_3168 hnum) (Freiman.workReverse20260919_s0005_records_3168_3200 hnum))

#print axioms solution
