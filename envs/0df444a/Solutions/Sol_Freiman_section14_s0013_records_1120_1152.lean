-- Prove2me | solution 1 for Freiman.section14_s0013_records_1120_1152
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T12:10:31.378478+00:00
-- url     : https://prove2.me/submissions/e5f08b9b-3610-4fe2-80d2-aabbf48b32f2

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
namespace Section14Records_13_1120_1152
private theorem valid1120 : RecordDataValid section14Catalog 13 (⟨47,(14),[1,2,5,13,14],[174],297⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨297,[1,2,3,5,13,14,15],298⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1121 : RecordDataValid section14Catalog 13 (⟨47,(14),[1,5,13],[186],321⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨321,[1,2,4,5,6,8,9,10,12,13,14,16],322⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1122 : RecordDataValid section14Catalog 13 (⟨47,(15),[1,2,5,6,13,14],[170,174,190],196⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨196,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],196⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1123 : RecordDataValid section14Catalog 13 (⟨47,(15),[1,5,13],[186],196⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨196,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],196⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1124 : RecordDataValid section14Catalog 13 (⟨47,(16),[1,2,5,6,13,14],[170,174,190],269⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨269,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],270⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1125 : RecordDataValid section14Catalog 13 (⟨47,(16),[1,5,13],[186],269⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨269,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],270⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1126 : RecordDataValid section14Catalog 13 (⟨47,(17),[1,2,5,6,13,14],[170],270⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨270,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],271⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1127 : RecordDataValid section14Catalog 13 (⟨47,(17),[1,2,5,6,13,14],[174],299⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨299,[1,2,3,5,6,7,13,14,15],300⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1128 : RecordDataValid section14Catalog 13 (⟨47,(17),[1,2,5,6,13,14],[190],323⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨323,[1,2,4,5,6,8,9,10,12,13,14,16],324⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1129 : RecordDataValid section14Catalog 13 (⟨47,(17),[1,5,13],[186],323⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨323,[1,2,4,5,6,8,9,10,12,13,14,16],324⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1130 : RecordDataValid section14Catalog 13 (⟨47,(18),[1,2,5,6,13,14],[170],270⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨270,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],271⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1131 : RecordDataValid section14Catalog 13 (⟨47,(18),[1,2,5,6,13,14],[174],299⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨299,[1,2,3,5,6,7,13,14,15],300⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1132 : RecordDataValid section14Catalog 13 (⟨47,(18),[1,2,5,6,13,14],[190],323⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨323,[1,2,4,5,6,8,9,10,12,13,14,16],324⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1133 : RecordDataValid section14Catalog 13 (⟨47,(18),[1,5,13],[186],323⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨323,[1,2,4,5,6,8,9,10,12,13,14,16],324⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1134 : RecordDataValid section14Catalog 13 (⟨47,(19),[1,2,5,6,13,14],[170],270⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨270,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],271⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1135 : RecordDataValid section14Catalog 13 (⟨47,(19),[1,2,5,6,13,14],[174],299⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨299,[1,2,3,5,6,7,13,14,15],300⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1136 : RecordDataValid section14Catalog 13 (⟨47,(19),[1,2,5,6,13,14],[190],323⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨323,[1,2,4,5,6,8,9,10,12,13,14,16],324⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1137 : RecordDataValid section14Catalog 13 (⟨47,(19),[1,5,13],[186],323⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨323,[1,2,4,5,6,8,9,10,12,13,14,16],324⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1138 : RecordDataValid section14Catalog 13 (⟨47,(20),[1,2,5,6,13,14],[170,174,190],198⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨198,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],198⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1139 : RecordDataValid section14Catalog 13 (⟨47,(20),[1,5,13],[186],198⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨198,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],198⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1140 : RecordDataValid section14Catalog 13 (⟨47,(21),[1,2,5,6,13,14],[170,174,190],271⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨271,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],272⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1141 : RecordDataValid section14Catalog 13 (⟨47,(21),[1,5,13],[186],271⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨271,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],272⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1142 : RecordDataValid section14Catalog 13 (⟨47,(22),[1,2,5,6,13,14],[170],272⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨272,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],273⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1143 : RecordDataValid section14Catalog 13 (⟨47,(22),[1,2,5,6,13,14],[174],300⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨300,[1,2,3,5,6,7,13,14,15],301⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1144 : RecordDataValid section14Catalog 13 (⟨47,(22),[1,2,5,6,13,14],[190],324⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨324,[1,2,4,5,6,8,9,10,12,13,14,16],325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1145 : RecordDataValid section14Catalog 13 (⟨47,(22),[1,5,13],[186],324⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨324,[1,2,4,5,6,8,9,10,12,13,14,16],325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1146 : RecordDataValid section14Catalog 13 (⟨47,(23),[1,2,5,6,13,14],[170],272⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨272,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],273⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1147 : RecordDataValid section14Catalog 13 (⟨47,(23),[1,2,5,6,13,14],[174],300⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨300,[1,2,3,5,6,7,13,14,15],301⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1148 : RecordDataValid section14Catalog 13 (⟨47,(23),[1,2,5,6,13,14],[190],324⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨324,[1,2,4,5,6,8,9,10,12,13,14,16],325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1149 : RecordDataValid section14Catalog 13 (⟨47,(23),[1,5,13],[186],324⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨324,[1,2,4,5,6,8,9,10,12,13,14,16],325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1150 : RecordDataValid section14Catalog 13 (⟨47,(24),[1,2,5,6,13,14],[170],272⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨272,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],273⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1151 : RecordDataValid section14Catalog 13 (⟨47,(24),[1,2,5,6,13,14],[174],300⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨300,[1,2,3,5,6,7,13,14,15],301⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1120).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1120).take 32 = [⟨47,(14),[1,2,5,13,14],[174],297⟩,⟨47,(14),[1,5,13],[186],321⟩,⟨47,(15),[1,2,5,6,13,14],[170,174,190],196⟩,⟨47,(15),[1,5,13],[186],196⟩,⟨47,(16),[1,2,5,6,13,14],[170,174,190],269⟩,⟨47,(16),[1,5,13],[186],269⟩,⟨47,(17),[1,2,5,6,13,14],[170],270⟩,⟨47,(17),[1,2,5,6,13,14],[174],299⟩,⟨47,(17),[1,2,5,6,13,14],[190],323⟩,⟨47,(17),[1,5,13],[186],323⟩,⟨47,(18),[1,2,5,6,13,14],[170],270⟩,⟨47,(18),[1,2,5,6,13,14],[174],299⟩,⟨47,(18),[1,2,5,6,13,14],[190],323⟩,⟨47,(18),[1,5,13],[186],323⟩,⟨47,(19),[1,2,5,6,13,14],[170],270⟩,⟨47,(19),[1,2,5,6,13,14],[174],299⟩,⟨47,(19),[1,2,5,6,13,14],[190],323⟩,⟨47,(19),[1,5,13],[186],323⟩,⟨47,(20),[1,2,5,6,13,14],[170,174,190],198⟩,⟨47,(20),[1,5,13],[186],198⟩,⟨47,(21),[1,2,5,6,13,14],[170,174,190],271⟩,⟨47,(21),[1,5,13],[186],271⟩,⟨47,(22),[1,2,5,6,13,14],[170],272⟩,⟨47,(22),[1,2,5,6,13,14],[174],300⟩,⟨47,(22),[1,2,5,6,13,14],[190],324⟩,⟨47,(22),[1,5,13],[186],324⟩,⟨47,(23),[1,2,5,6,13,14],[170],272⟩,⟨47,(23),[1,2,5,6,13,14],[174],300⟩,⟨47,(23),[1,2,5,6,13,14],[190],324⟩,⟨47,(23),[1,5,13],[186],324⟩,⟨47,(24),[1,2,5,6,13,14],[170],272⟩,⟨47,(24),[1,2,5,6,13,14],[174],300⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1120
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1121
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1122
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1123
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1124
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1125
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1126
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1127
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1128
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1129
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1130
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1131
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1132
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1133
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1134
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1135
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1136
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1137
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1138
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1139
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1140
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1141
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1142
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1143
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1144
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1145
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1146
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1147
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1148
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1149
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1150
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1151
end Section14Records_13_1120_1152

#print axioms solution
