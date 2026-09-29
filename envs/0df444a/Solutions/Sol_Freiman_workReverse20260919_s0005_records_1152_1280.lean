-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_1152_1280
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:11:00.906367+00:00
-- url     : https://prove2.me/submissions/5f66aeb8-5121-43f7-966e-264b50fb63bd

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_1152_1184
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_1152_1184
private theorem valid1152 : RecordDataValid section14Catalog 5 (⟨42,(13),[1,2,5,6,13,14],[174],292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨292,[1,2,3,5,6,7,13,14,15],293⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1153 : RecordDataValid section14Catalog 5 (⟨42,(13),[1,2,5,6,13,14],[190],316⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨316,[1,2,4,5,6,8,13,14,16],317⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1154 : RecordDataValid section14Catalog 5 (⟨42,(13),[1,5,13],[186],316⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨316,[1,2,4,5,6,8,13,14,16],317⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1155 : RecordDataValid section14Catalog 5 (⟨42,(14),[1,2,5,6,13,14],[170],256⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨256,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],257⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1156 : RecordDataValid section14Catalog 5 (⟨42,(14),[1,2,5,6,13,14],[174],291⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨291,[1,2,3,5,6,7,13,14,15],292⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1157 : RecordDataValid section14Catalog 5 (⟨42,(14),[1,2,5,6,13,14],[190],315⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨315,[1,2,4,5,6,8,9,10,12,13,14,16],316⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1158 : RecordDataValid section14Catalog 5 (⟨42,(14),[1,5,13],[186],315⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨315,[1,2,4,5,6,8,9,10,12,13,14,16],316⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1159 : RecordDataValid section14Catalog 5 (⟨42,(15),[1,2,5,6,13,14],[170],258⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨258,[1,2,3,4,5,6,7,8,13,14,15,16],259⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1160 : RecordDataValid section14Catalog 5 (⟨42,(15),[1,2,5,6,13,14],[174],293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨293,[1,2,3,5,6,7,13,14,15],294⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1161 : RecordDataValid section14Catalog 5 (⟨42,(15),[1,2,5,6,13,14],[190],317⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨317,[1,2,4,5,6,8,13,14,16],318⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1162 : RecordDataValid section14Catalog 5 (⟨42,(15),[1,5,13],[186],317⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨317,[1,2,4,5,6,8,13,14,16],318⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1163 : RecordDataValid section14Catalog 5 (⟨42,(16),[1,2,5,6,13,14],[170],258⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨258,[1,2,3,4,5,6,7,8,13,14,15,16],259⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1164 : RecordDataValid section14Catalog 5 (⟨42,(16),[1,2,5,6,13,14],[174],293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨293,[1,2,3,5,6,7,13,14,15],294⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1165 : RecordDataValid section14Catalog 5 (⟨42,(16),[1,2,5,6,13,14],[190],317⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨317,[1,2,4,5,6,8,13,14,16],318⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1166 : RecordDataValid section14Catalog 5 (⟨42,(16),[1,5,13],[186],317⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨317,[1,2,4,5,6,8,13,14,16],318⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1167 : RecordDataValid section14Catalog 5 (⟨42,(17),[1,2,5,6,13,14],[170],258⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨258,[1,2,3,4,5,6,7,8,13,14,15,16],259⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1168 : RecordDataValid section14Catalog 5 (⟨42,(17),[1,2,5,6,13,14],[174],293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨293,[1,2,3,5,6,7,13,14,15],294⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1169 : RecordDataValid section14Catalog 5 (⟨42,(17),[1,2,5,6,13,14],[190],317⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨317,[1,2,4,5,6,8,13,14,16],318⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1170 : RecordDataValid section14Catalog 5 (⟨42,(17),[1,5,13],[186],317⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨317,[1,2,4,5,6,8,13,14,16],318⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1171 : RecordDataValid section14Catalog 5 (⟨42,(18),[1,2,5,6,13,14],[170],258⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨258,[1,2,3,4,5,6,7,8,13,14,15,16],259⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1172 : RecordDataValid section14Catalog 5 (⟨42,(18),[1,2,5,6,13,14],[174],293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨293,[1,2,3,5,6,7,13,14,15],294⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1173 : RecordDataValid section14Catalog 5 (⟨42,(18),[1,2,5,6,13,14],[190],317⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨317,[1,2,4,5,6,8,13,14,16],318⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1174 : RecordDataValid section14Catalog 5 (⟨42,(18),[1,5,13],[186],317⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨317,[1,2,4,5,6,8,13,14,16],318⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1175 : RecordDataValid section14Catalog 5 (⟨42,(19),[1,2,5,6,13,14],[170],258⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨258,[1,2,3,4,5,6,7,8,13,14,15,16],259⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1176 : RecordDataValid section14Catalog 5 (⟨42,(19),[1,2,5,6,13,14],[174],293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨293,[1,2,3,5,6,7,13,14,15],294⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1177 : RecordDataValid section14Catalog 5 (⟨42,(19),[1,2,5,6,13,14],[190],317⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨317,[1,2,4,5,6,8,13,14,16],318⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1178 : RecordDataValid section14Catalog 5 (⟨42,(19),[1,5,13],[186],317⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨317,[1,2,4,5,6,8,13,14,16],318⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1179 : RecordDataValid section14Catalog 5 (⟨42,(20),[1,2,5,6,13,14],[170],259⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨259,[1,2,3,4,5,6,7,8,13,14,15,16],260⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1180 : RecordDataValid section14Catalog 5 (⟨42,(20),[1,2,5,6,13,14],[174],294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨294,[1,2,3,5,6,7,13,14,15],295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1181 : RecordDataValid section14Catalog 5 (⟨42,(20),[1,2,5,6,13,14],[190],318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨318,[1,2,4,5,6,8,13,14,16],319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1182 : RecordDataValid section14Catalog 5 (⟨42,(20),[1,5,13],[186],318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨318,[1,2,4,5,6,8,13,14,16],319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1183 : RecordDataValid section14Catalog 5 (⟨42,(21),[1,2,5,6,13,14],[170],259⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨259,[1,2,3,4,5,6,7,8,13,14,15,16],260⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_1152_1184 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 1152).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 1152).take 32 = [⟨42,(13),[1,2,5,6,13,14],[174],292⟩,⟨42,(13),[1,2,5,6,13,14],[190],316⟩,⟨42,(13),[1,5,13],[186],316⟩,⟨42,(14),[1,2,5,6,13,14],[170],256⟩,⟨42,(14),[1,2,5,6,13,14],[174],291⟩,⟨42,(14),[1,2,5,6,13,14],[190],315⟩,⟨42,(14),[1,5,13],[186],315⟩,⟨42,(15),[1,2,5,6,13,14],[170],258⟩,⟨42,(15),[1,2,5,6,13,14],[174],293⟩,⟨42,(15),[1,2,5,6,13,14],[190],317⟩,⟨42,(15),[1,5,13],[186],317⟩,⟨42,(16),[1,2,5,6,13,14],[170],258⟩,⟨42,(16),[1,2,5,6,13,14],[174],293⟩,⟨42,(16),[1,2,5,6,13,14],[190],317⟩,⟨42,(16),[1,5,13],[186],317⟩,⟨42,(17),[1,2,5,6,13,14],[170],258⟩,⟨42,(17),[1,2,5,6,13,14],[174],293⟩,⟨42,(17),[1,2,5,6,13,14],[190],317⟩,⟨42,(17),[1,5,13],[186],317⟩,⟨42,(18),[1,2,5,6,13,14],[170],258⟩,⟨42,(18),[1,2,5,6,13,14],[174],293⟩,⟨42,(18),[1,2,5,6,13,14],[190],317⟩,⟨42,(18),[1,5,13],[186],317⟩,⟨42,(19),[1,2,5,6,13,14],[170],258⟩,⟨42,(19),[1,2,5,6,13,14],[174],293⟩,⟨42,(19),[1,2,5,6,13,14],[190],317⟩,⟨42,(19),[1,5,13],[186],317⟩,⟨42,(20),[1,2,5,6,13,14],[170],259⟩,⟨42,(20),[1,2,5,6,13,14],[174],294⟩,⟨42,(20),[1,2,5,6,13,14],[190],318⟩,⟨42,(20),[1,5,13],[186],318⟩,⟨42,(21),[1,2,5,6,13,14],[170],259⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1152
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1153
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1154
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1155
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1156
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1157
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1158
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1159
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1160
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1161
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1162
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1163
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1164
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1165
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1166
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1167
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1168
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1169
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1170
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1171
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1172
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1173
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1174
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1175
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1176
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1177
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1178
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1179
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1180
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1181
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1182
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1183
end Section14Records_5_1152_1184

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_1152_1184


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_1184_1216
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_1184_1216
private theorem valid1184 : RecordDataValid section14Catalog 5 (⟨42,(21),[1,2,5,6,13,14],[174],294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨294,[1,2,3,5,6,7,13,14,15],295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1185 : RecordDataValid section14Catalog 5 (⟨42,(21),[1,2,5,6,13,14],[190],318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨318,[1,2,4,5,6,8,13,14,16],319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1186 : RecordDataValid section14Catalog 5 (⟨42,(21),[1,5,13],[186],318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨318,[1,2,4,5,6,8,13,14,16],319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1187 : RecordDataValid section14Catalog 5 (⟨42,(22),[1,2,5,6,13,14],[170],259⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨259,[1,2,3,4,5,6,7,8,13,14,15,16],260⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1188 : RecordDataValid section14Catalog 5 (⟨42,(22),[1,2,5,6,13,14],[174],294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨294,[1,2,3,5,6,7,13,14,15],295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1189 : RecordDataValid section14Catalog 5 (⟨42,(22),[1,2,5,6,13,14],[190],318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨318,[1,2,4,5,6,8,13,14,16],319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1190 : RecordDataValid section14Catalog 5 (⟨42,(22),[1,5,13],[186],318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨318,[1,2,4,5,6,8,13,14,16],319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1191 : RecordDataValid section14Catalog 5 (⟨42,(23),[1,2,5,6,13,14],[170],259⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨259,[1,2,3,4,5,6,7,8,13,14,15,16],260⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1192 : RecordDataValid section14Catalog 5 (⟨42,(23),[1,2,5,6,13,14],[174],294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨294,[1,2,3,5,6,7,13,14,15],295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1193 : RecordDataValid section14Catalog 5 (⟨42,(23),[1,2,5,6,13,14],[190],318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨318,[1,2,4,5,6,8,13,14,16],319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1194 : RecordDataValid section14Catalog 5 (⟨42,(23),[1,5,13],[186],318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨318,[1,2,4,5,6,8,13,14,16],319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1195 : RecordDataValid section14Catalog 5 (⟨42,(24),[1,2,5,6,13,14],[170],259⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨259,[1,2,3,4,5,6,7,8,13,14,15,16],260⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1196 : RecordDataValid section14Catalog 5 (⟨42,(24),[1,2,5,6,13,14],[174],294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨294,[1,2,3,5,6,7,13,14,15],295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1197 : RecordDataValid section14Catalog 5 (⟨42,(24),[1,2,5,6,13,14],[190],318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨318,[1,2,4,5,6,8,13,14,16],319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1198 : RecordDataValid section14Catalog 5 (⟨42,(24),[1,5,13],[186],318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨318,[1,2,4,5,6,8,13,14,16],319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1199 : RecordDataValid section14Catalog 5 (⟨45,(0),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1200 : RecordDataValid section14Catalog 5 (⟨45,(0),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1201 : RecordDataValid section14Catalog 5 (⟨45,(1),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1202 : RecordDataValid section14Catalog 5 (⟨45,(1),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1203 : RecordDataValid section14Catalog 5 (⟨45,(2),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1204 : RecordDataValid section14Catalog 5 (⟨45,(2),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1205 : RecordDataValid section14Catalog 5 (⟨45,(3),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1206 : RecordDataValid section14Catalog 5 (⟨45,(3),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1207 : RecordDataValid section14Catalog 5 (⟨45,(4),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1208 : RecordDataValid section14Catalog 5 (⟨45,(4),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1209 : RecordDataValid section14Catalog 5 (⟨45,(5),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1210 : RecordDataValid section14Catalog 5 (⟨45,(5),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1211 : RecordDataValid section14Catalog 5 (⟨45,(6),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1212 : RecordDataValid section14Catalog 5 (⟨45,(6),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1213 : RecordDataValid section14Catalog 5 (⟨45,(7),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1214 : RecordDataValid section14Catalog 5 (⟨45,(7),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1215 : RecordDataValid section14Catalog 5 (⟨45,(8),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_1184_1216 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 1184).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 1184).take 32 = [⟨42,(21),[1,2,5,6,13,14],[174],294⟩,⟨42,(21),[1,2,5,6,13,14],[190],318⟩,⟨42,(21),[1,5,13],[186],318⟩,⟨42,(22),[1,2,5,6,13,14],[170],259⟩,⟨42,(22),[1,2,5,6,13,14],[174],294⟩,⟨42,(22),[1,2,5,6,13,14],[190],318⟩,⟨42,(22),[1,5,13],[186],318⟩,⟨42,(23),[1,2,5,6,13,14],[170],259⟩,⟨42,(23),[1,2,5,6,13,14],[174],294⟩,⟨42,(23),[1,2,5,6,13,14],[190],318⟩,⟨42,(23),[1,5,13],[186],318⟩,⟨42,(24),[1,2,5,6,13,14],[170],259⟩,⟨42,(24),[1,2,5,6,13,14],[174],294⟩,⟨42,(24),[1,2,5,6,13,14],[190],318⟩,⟨42,(24),[1,5,13],[186],318⟩,⟨45,(0),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(0),[1,5,13],[186],2⟩,⟨45,(1),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(1),[1,5,13],[186],2⟩,⟨45,(2),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(2),[1,5,13],[186],2⟩,⟨45,(3),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(3),[1,5,13],[186],2⟩,⟨45,(4),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(4),[1,5,13],[186],2⟩,⟨45,(5),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(5),[1,5,13],[186],2⟩,⟨45,(6),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(6),[1,5,13],[186],2⟩,⟨45,(7),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(7),[1,5,13],[186],2⟩,⟨45,(8),[1,2,5,6,13,14],[170,174,190],2⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1184
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1185
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1186
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1187
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1188
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1189
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1190
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1191
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1192
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1193
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1194
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1195
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1196
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1197
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1198
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1199
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1200
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1201
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1202
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1203
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1204
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1205
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1206
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1207
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1208
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1209
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1210
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1211
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1212
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1213
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1214
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1215
end Section14Records_5_1184_1216

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_1184_1216


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_1216_1248
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_1216_1248
private theorem valid1216 : RecordDataValid section14Catalog 5 (⟨45,(8),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1217 : RecordDataValid section14Catalog 5 (⟨45,(9),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1218 : RecordDataValid section14Catalog 5 (⟨45,(9),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1219 : RecordDataValid section14Catalog 5 (⟨45,(10),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1220 : RecordDataValid section14Catalog 5 (⟨45,(10),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1221 : RecordDataValid section14Catalog 5 (⟨45,(11),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1222 : RecordDataValid section14Catalog 5 (⟨45,(11),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1223 : RecordDataValid section14Catalog 5 (⟨45,(12),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1224 : RecordDataValid section14Catalog 5 (⟨45,(12),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1225 : RecordDataValid section14Catalog 5 (⟨45,(13),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1226 : RecordDataValid section14Catalog 5 (⟨45,(13),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1227 : RecordDataValid section14Catalog 5 (⟨45,(14),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1228 : RecordDataValid section14Catalog 5 (⟨45,(14),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1229 : RecordDataValid section14Catalog 5 (⟨45,(15),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1230 : RecordDataValid section14Catalog 5 (⟨45,(15),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1231 : RecordDataValid section14Catalog 5 (⟨45,(16),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1232 : RecordDataValid section14Catalog 5 (⟨45,(16),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1233 : RecordDataValid section14Catalog 5 (⟨45,(17),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1234 : RecordDataValid section14Catalog 5 (⟨45,(17),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1235 : RecordDataValid section14Catalog 5 (⟨45,(18),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1236 : RecordDataValid section14Catalog 5 (⟨45,(18),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1237 : RecordDataValid section14Catalog 5 (⟨45,(19),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1238 : RecordDataValid section14Catalog 5 (⟨45,(19),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1239 : RecordDataValid section14Catalog 5 (⟨45,(20),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1240 : RecordDataValid section14Catalog 5 (⟨45,(20),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1241 : RecordDataValid section14Catalog 5 (⟨45,(21),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1242 : RecordDataValid section14Catalog 5 (⟨45,(21),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1243 : RecordDataValid section14Catalog 5 (⟨45,(22),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1244 : RecordDataValid section14Catalog 5 (⟨45,(22),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1245 : RecordDataValid section14Catalog 5 (⟨45,(23),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1246 : RecordDataValid section14Catalog 5 (⟨45,(23),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1247 : RecordDataValid section14Catalog 5 (⟨45,(24),[1,2,5,6,13,14],[170,174,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_1216_1248 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 1216).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 1216).take 32 = [⟨45,(8),[1,5,13],[186],2⟩,⟨45,(9),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(9),[1,5,13],[186],2⟩,⟨45,(10),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(10),[1,5,13],[186],2⟩,⟨45,(11),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(11),[1,5,13],[186],2⟩,⟨45,(12),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(12),[1,5,13],[186],2⟩,⟨45,(13),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(13),[1,5,13],[186],2⟩,⟨45,(14),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(14),[1,5,13],[186],2⟩,⟨45,(15),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(15),[1,5,13],[186],2⟩,⟨45,(16),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(16),[1,5,13],[186],2⟩,⟨45,(17),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(17),[1,5,13],[186],2⟩,⟨45,(18),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(18),[1,5,13],[186],2⟩,⟨45,(19),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(19),[1,5,13],[186],2⟩,⟨45,(20),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(20),[1,5,13],[186],2⟩,⟨45,(21),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(21),[1,5,13],[186],2⟩,⟨45,(22),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(22),[1,5,13],[186],2⟩,⟨45,(23),[1,2,5,6,13,14],[170,174,190],2⟩,⟨45,(23),[1,5,13],[186],2⟩,⟨45,(24),[1,2,5,6,13,14],[170,174,190],2⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1216
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1217
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1218
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1219
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1220
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1221
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1222
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1223
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1224
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1225
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1226
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1227
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1228
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1229
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1230
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1231
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1232
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1233
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1234
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1235
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1236
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1237
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1238
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1239
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1240
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1241
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1242
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1243
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1244
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1245
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1246
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1247
end Section14Records_5_1216_1248

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_1216_1248


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_1248_1280
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_1248_1280
private theorem valid1248 : RecordDataValid section14Catalog 5 (⟨45,(24),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1249 : RecordDataValid section14Catalog 5 (⟨47,(0),[1,2,5,6,13,14],[170,174,190],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1250 : RecordDataValid section14Catalog 5 (⟨47,(0),[1,5,13],[186],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1251 : RecordDataValid section14Catalog 5 (⟨47,(1),[1,2,5,6,13,14],[170,174,190],260⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨260,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],261⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1252 : RecordDataValid section14Catalog 5 (⟨47,(1),[1,5,13],[186],260⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨260,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],261⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1253 : RecordDataValid section14Catalog 5 (⟨47,(2),[1,2,5,6,13,14],[170,174,190],261⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨261,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],262⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1254 : RecordDataValid section14Catalog 5 (⟨47,(2),[1,5,13],[186],261⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨261,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],262⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1255 : RecordDataValid section14Catalog 5 (⟨47,(3),[1,2,5,6,13,14],[170,174,190],262⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨262,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],263⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1256 : RecordDataValid section14Catalog 5 (⟨47,(3),[1,5,13],[186],262⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨262,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],263⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1257 : RecordDataValid section14Catalog 5 (⟨47,(4),[1,2,5,6,13,14],[170,174,190],263⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨263,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],264⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1258 : RecordDataValid section14Catalog 5 (⟨47,(4),[1,5,13],[186],263⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨263,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],264⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1259 : RecordDataValid section14Catalog 5 (⟨47,(5),[1,2,5,6,13,14],[170,174,190],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1260 : RecordDataValid section14Catalog 5 (⟨47,(5),[1,5,13],[186],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1261 : RecordDataValid section14Catalog 5 (⟨47,(6),[1,2,5,6,13,14],[170,174,190],260⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨260,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],261⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1262 : RecordDataValid section14Catalog 5 (⟨47,(6),[1,5,13],[186],260⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨260,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],261⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1263 : RecordDataValid section14Catalog 5 (⟨47,(7),[1,2,5,6,13,14],[170],264⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨264,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],265⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1264 : RecordDataValid section14Catalog 5 (⟨47,(7),[1,2,5,6,13,14],[190],319⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨319,[1,2,4,5,6,8,9,10,12,13,14,16],320⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1265 : RecordDataValid section14Catalog 5 (⟨47,(7),[1,2,5,13,14],[174],295⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨295,[1,2,3,5,13,14,15],296⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1266 : RecordDataValid section14Catalog 5 (⟨47,(7),[1,5,13],[186],319⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨319,[1,2,4,5,6,8,9,10,12,13,14,16],320⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1267 : RecordDataValid section14Catalog 5 (⟨47,(8),[1,2,5,6,13,14],[170],265⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨265,[1,2,3,4,5,6,7,10,11,13,14,15,16],266⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1268 : RecordDataValid section14Catalog 5 (⟨47,(8),[1,2,5,6,13,14],[190],320⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨320,[1,2,4,5,6,8,9,10,12,13,14,16],321⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1269 : RecordDataValid section14Catalog 5 (⟨47,(8),[1,5,13],[186],320⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨320,[1,2,4,5,6,8,9,10,12,13,14,16],321⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1270 : RecordDataValid section14Catalog 5 (⟨47,(8),[5,6],[174],265⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨265,[1,2,3,4,5,6,7,10,11,13,14,15,16],266⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1271 : RecordDataValid section14Catalog 5 (⟨47,(9),[1,2,5,6,13,14],[170],266⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨266,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],267⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1272 : RecordDataValid section14Catalog 5 (⟨47,(9),[1,2,5,6,13,14],[190],321⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨321,[1,2,4,5,6,8,9,10,12,13,14,16],322⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1273 : RecordDataValid section14Catalog 5 (⟨47,(9),[1,2,5,13,14],[174],297⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨297,[1,2,3,5,13,14,15],298⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1274 : RecordDataValid section14Catalog 5 (⟨47,(9),[1,5,13],[186],321⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨321,[1,2,4,5,6,8,9,10,12,13,14,16],322⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1275 : RecordDataValid section14Catalog 5 (⟨47,(10),[1,2,5,6,13,14],[170,174,190],194⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨194,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],194⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1276 : RecordDataValid section14Catalog 5 (⟨47,(10),[1,5,13],[186],194⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨194,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],194⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1277 : RecordDataValid section14Catalog 5 (⟨47,(11),[1,2,5,6,13,14],[170,174,190],267⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨267,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],268⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1278 : RecordDataValid section14Catalog 5 (⟨47,(11),[1,5,13],[186],267⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨267,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],268⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1279 : RecordDataValid section14Catalog 5 (⟨47,(12),[1,2,5,6,13,14],[170],268⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨268,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],269⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_1248_1280 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 1248).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 1248).take 32 = [⟨45,(24),[1,5,13],[186],2⟩,⟨47,(0),[1,2,5,6,13,14],[170,174,190],189⟩,⟨47,(0),[1,5,13],[186],189⟩,⟨47,(1),[1,2,5,6,13,14],[170,174,190],260⟩,⟨47,(1),[1,5,13],[186],260⟩,⟨47,(2),[1,2,5,6,13,14],[170,174,190],261⟩,⟨47,(2),[1,5,13],[186],261⟩,⟨47,(3),[1,2,5,6,13,14],[170,174,190],262⟩,⟨47,(3),[1,5,13],[186],262⟩,⟨47,(4),[1,2,5,6,13,14],[170,174,190],263⟩,⟨47,(4),[1,5,13],[186],263⟩,⟨47,(5),[1,2,5,6,13,14],[170,174,190],189⟩,⟨47,(5),[1,5,13],[186],189⟩,⟨47,(6),[1,2,5,6,13,14],[170,174,190],260⟩,⟨47,(6),[1,5,13],[186],260⟩,⟨47,(7),[1,2,5,6,13,14],[170],264⟩,⟨47,(7),[1,2,5,6,13,14],[190],319⟩,⟨47,(7),[1,2,5,13,14],[174],295⟩,⟨47,(7),[1,5,13],[186],319⟩,⟨47,(8),[1,2,5,6,13,14],[170],265⟩,⟨47,(8),[1,2,5,6,13,14],[190],320⟩,⟨47,(8),[1,5,13],[186],320⟩,⟨47,(8),[5,6],[174],265⟩,⟨47,(9),[1,2,5,6,13,14],[170],266⟩,⟨47,(9),[1,2,5,6,13,14],[190],321⟩,⟨47,(9),[1,2,5,13,14],[174],297⟩,⟨47,(9),[1,5,13],[186],321⟩,⟨47,(10),[1,2,5,6,13,14],[170,174,190],194⟩,⟨47,(10),[1,5,13],[186],194⟩,⟨47,(11),[1,2,5,6,13,14],[170,174,190],267⟩,⟨47,(11),[1,5,13],[186],267⟩,⟨47,(12),[1,2,5,6,13,14],[170],268⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1248
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1249
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1250
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1251
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1252
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1253
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1254
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1255
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1256
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1257
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1258
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1259
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1260
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1261
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1262
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1263
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1264
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1265
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1266
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1267
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1268
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1269
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1270
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1271
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1272
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1273
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1274
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1275
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1276
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1277
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1278
  · exact recordValid_of_data section14Catalog 5 _ hnum valid1279
end Section14Records_5_1248_1280

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_1248_1280

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 1152).take 128, section14RecordValid section14Catalog 5 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (5 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 5 r
  exact (all_of_interval_split P xs 1152 1216 1280 (by decide) (by decide) (all_of_interval_split P xs 1152 1184 1216 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_1152_1184 hnum) (Freiman.workReverse20260919_s0005_records_1184_1216 hnum)) (all_of_interval_split P xs 1216 1248 1280 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_1216_1248 hnum) (Freiman.workReverse20260919_s0005_records_1248_1280 hnum)))

#print axioms solution
