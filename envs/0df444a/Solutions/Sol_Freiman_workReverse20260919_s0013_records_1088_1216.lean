-- Prove2me | solution 1 for Freiman.workReverse20260919_s0013_records_1088_1216
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:53:58.962362+00:00
-- url     : https://prove2.me/submissions/8d408cda-66b6-418c-8d8c-375e25922976

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_1088_1120
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_1088_1120
private theorem valid1088 : RecordDataValid section14Catalog 13 (⟨47,(4),[1,2,5,6,13,14],[170,174,190],263⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨263,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],264⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1089 : RecordDataValid section14Catalog 13 (⟨47,(4),[1,5,13],[186],263⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨263,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],264⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1090 : RecordDataValid section14Catalog 13 (⟨47,(5),[1,2,5,6,13,14],[170,174,190],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1091 : RecordDataValid section14Catalog 13 (⟨47,(5),[1,5,13],[186],189⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨189,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],189⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1092 : RecordDataValid section14Catalog 13 (⟨47,(6),[1,2,5,6,13,14],[170,174,190],260⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨260,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],261⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1093 : RecordDataValid section14Catalog 13 (⟨47,(6),[1,5,13],[186],260⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨260,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],261⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1094 : RecordDataValid section14Catalog 13 (⟨47,(7),[1,2,5,6,13,14],[170],264⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨264,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],265⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1095 : RecordDataValid section14Catalog 13 (⟨47,(7),[1,2,5,6,13,14],[190],319⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨319,[1,2,4,5,6,8,9,10,12,13,14,16],320⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1096 : RecordDataValid section14Catalog 13 (⟨47,(7),[1,2,5,13,14],[174],295⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨295,[1,2,3,5,13,14,15],296⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1097 : RecordDataValid section14Catalog 13 (⟨47,(7),[1,5,13],[186],319⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨319,[1,2,4,5,6,8,9,10,12,13,14,16],320⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1098 : RecordDataValid section14Catalog 13 (⟨47,(8),[1,2,5,6,13,14],[170],265⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨265,[1,2,3,4,5,6,7,10,11,13,14,15,16],266⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1099 : RecordDataValid section14Catalog 13 (⟨47,(8),[1,2,5,6,13,14],[190],320⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨320,[1,2,4,5,6,8,9,10,12,13,14,16],321⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1100 : RecordDataValid section14Catalog 13 (⟨47,(8),[1,2,13,14],[174],296⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨296,[1,2,13,14,15],297⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1101 : RecordDataValid section14Catalog 13 (⟨47,(8),[1,5,13],[186],320⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨320,[1,2,4,5,6,8,9,10,12,13,14,16],321⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1102 : RecordDataValid section14Catalog 13 (⟨47,(9),[1,2,5,6,13,14],[170],266⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨266,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],267⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1103 : RecordDataValid section14Catalog 13 (⟨47,(9),[1,2,5,6,13,14],[190],321⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨321,[1,2,4,5,6,8,9,10,12,13,14,16],322⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1104 : RecordDataValid section14Catalog 13 (⟨47,(9),[1,2,5,13,14],[174],297⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨297,[1,2,3,5,13,14,15],298⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1105 : RecordDataValid section14Catalog 13 (⟨47,(9),[1,5,13],[186],321⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨321,[1,2,4,5,6,8,9,10,12,13,14,16],322⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1106 : RecordDataValid section14Catalog 13 (⟨47,(10),[1,2,5,6,13,14],[170,174,190],194⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨194,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],194⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1107 : RecordDataValid section14Catalog 13 (⟨47,(10),[1,5,13],[186],194⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨194,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],194⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1108 : RecordDataValid section14Catalog 13 (⟨47,(11),[1,2,5,6,13,14],[170,174,190],267⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨267,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],268⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1109 : RecordDataValid section14Catalog 13 (⟨47,(11),[1,5,13],[186],267⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨267,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],268⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1110 : RecordDataValid section14Catalog 13 (⟨47,(12),[1,2,5,6,13,14],[170],268⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨268,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],269⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1111 : RecordDataValid section14Catalog 13 (⟨47,(12),[1,2,5,6,13,14],[190],322⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨322,[1,2,4,5,6,8,9,10,12,13,14,16],323⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1112 : RecordDataValid section14Catalog 13 (⟨47,(12),[1,2,5,13,14],[174],298⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨298,[1,2,3,5,6,7,13,14,15],299⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1113 : RecordDataValid section14Catalog 13 (⟨47,(12),[1,5,13],[186],322⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨322,[1,2,4,5,6,8,9,10,12,13,14,16],323⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1114 : RecordDataValid section14Catalog 13 (⟨47,(13),[1,2,5,6,13,14],[170],268⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨268,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],269⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1115 : RecordDataValid section14Catalog 13 (⟨47,(13),[1,2,5,6,13,14],[190],322⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨322,[1,2,4,5,6,8,9,10,12,13,14,16],323⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1116 : RecordDataValid section14Catalog 13 (⟨47,(13),[1,2,5,13,14],[174],298⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨298,[1,2,3,5,6,7,13,14,15],299⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1117 : RecordDataValid section14Catalog 13 (⟨47,(13),[1,5,13],[186],322⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨322,[1,2,4,5,6,8,9,10,12,13,14,16],323⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1118 : RecordDataValid section14Catalog 13 (⟨47,(14),[1,2,5,6,13,14],[170],266⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨266,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],267⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1119 : RecordDataValid section14Catalog 13 (⟨47,(14),[1,2,5,6,13,14],[190],321⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨321,[1,2,4,5,6,8,9,10,12,13,14,16],322⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_1088_1120 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1088).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1088).take 32 = [⟨47,(4),[1,2,5,6,13,14],[170,174,190],263⟩,⟨47,(4),[1,5,13],[186],263⟩,⟨47,(5),[1,2,5,6,13,14],[170,174,190],189⟩,⟨47,(5),[1,5,13],[186],189⟩,⟨47,(6),[1,2,5,6,13,14],[170,174,190],260⟩,⟨47,(6),[1,5,13],[186],260⟩,⟨47,(7),[1,2,5,6,13,14],[170],264⟩,⟨47,(7),[1,2,5,6,13,14],[190],319⟩,⟨47,(7),[1,2,5,13,14],[174],295⟩,⟨47,(7),[1,5,13],[186],319⟩,⟨47,(8),[1,2,5,6,13,14],[170],265⟩,⟨47,(8),[1,2,5,6,13,14],[190],320⟩,⟨47,(8),[1,2,13,14],[174],296⟩,⟨47,(8),[1,5,13],[186],320⟩,⟨47,(9),[1,2,5,6,13,14],[170],266⟩,⟨47,(9),[1,2,5,6,13,14],[190],321⟩,⟨47,(9),[1,2,5,13,14],[174],297⟩,⟨47,(9),[1,5,13],[186],321⟩,⟨47,(10),[1,2,5,6,13,14],[170,174,190],194⟩,⟨47,(10),[1,5,13],[186],194⟩,⟨47,(11),[1,2,5,6,13,14],[170,174,190],267⟩,⟨47,(11),[1,5,13],[186],267⟩,⟨47,(12),[1,2,5,6,13,14],[170],268⟩,⟨47,(12),[1,2,5,6,13,14],[190],322⟩,⟨47,(12),[1,2,5,13,14],[174],298⟩,⟨47,(12),[1,5,13],[186],322⟩,⟨47,(13),[1,2,5,6,13,14],[170],268⟩,⟨47,(13),[1,2,5,6,13,14],[190],322⟩,⟨47,(13),[1,2,5,13,14],[174],298⟩,⟨47,(13),[1,5,13],[186],322⟩,⟨47,(14),[1,2,5,6,13,14],[170],266⟩,⟨47,(14),[1,2,5,6,13,14],[190],321⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1088
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1089
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1090
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1091
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1092
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1093
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1094
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1095
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1096
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1097
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1098
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1099
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1100
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1101
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1102
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1103
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1104
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1105
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1106
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1107
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1108
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1109
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1110
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1111
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1112
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1113
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1114
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1115
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1116
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1117
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1118
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1119
end Section14Records_13_1088_1120

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_1088_1120


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_1120_1152
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
theorem _root_.Freiman.workReverse20260919_s0013_records_1120_1152 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1120).take 32, section14RecordValid section14Catalog 13 r := by
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

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_1120_1152


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_1152_1184
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_1152_1184
private theorem valid1152 : RecordDataValid section14Catalog 13 (⟨47,(24),[1,2,5,6,13,14],[190],324⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨324,[1,2,4,5,6,8,9,10,12,13,14,16],325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1153 : RecordDataValid section14Catalog 13 (⟨47,(24),[1,5,13],[186],324⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨324,[1,2,4,5,6,8,9,10,12,13,14,16],325⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1154 : RecordDataValid section14Catalog 13 (⟨55,(0),[1,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1155 : RecordDataValid section14Catalog 13 (⟨55,(0),[1,5,13],[186],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1156 : RecordDataValid section14Catalog 13 (⟨55,(0),[2,6,13,14],[170,174],97⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨97,[1,2,5,6,9,10,13,14],97⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1157 : RecordDataValid section14Catalog 13 (⟨55,(1),[1,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1158 : RecordDataValid section14Catalog 13 (⟨55,(1),[1,5,13],[186],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1159 : RecordDataValid section14Catalog 13 (⟨55,(2),[6,13],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1160 : RecordDataValid section14Catalog 13 (⟨55,(2),[13],[170,174,186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1161 : RecordDataValid section14Catalog 13 (⟨55,(3),[1,6,13],[170,174],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1162 : RecordDataValid section14Catalog 13 (⟨55,(3),[13],[186,190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1163 : RecordDataValid section14Catalog 13 (⟨55,(4),[1,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1164 : RecordDataValid section14Catalog 13 (⟨55,(4),[1,5,13],[186],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1165 : RecordDataValid section14Catalog 13 (⟨55,(5),[1,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1166 : RecordDataValid section14Catalog 13 (⟨55,(5),[1,5,13],[186],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1167 : RecordDataValid section14Catalog 13 (⟨55,(6),[1,2,5,6,13,14],[170,174],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1168 : RecordDataValid section14Catalog 13 (⟨55,(6),[6,13],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1169 : RecordDataValid section14Catalog 13 (⟨55,(6),[13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1170 : RecordDataValid section14Catalog 13 (⟨55,(7),[1,2,5,6,13,14],[190],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1171 : RecordDataValid section14Catalog 13 (⟨55,(7),[1,5,13],[186],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1172 : RecordDataValid section14Catalog 13 (⟨55,(7),[1,6,13],[170,174],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1173 : RecordDataValid section14Catalog 13 (⟨55,(8),[1,2,5,6,13,14],[190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1174 : RecordDataValid section14Catalog 13 (⟨55,(8),[1,5,13],[186],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1175 : RecordDataValid section14Catalog 13 (⟨55,(8),[5,6,13,14],[170,174],97⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨97,[1,2,5,6,9,10,13,14],97⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1176 : RecordDataValid section14Catalog 13 (⟨55,(9),[1,2,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1177 : RecordDataValid section14Catalog 13 (⟨55,(9),[1,5,13],[186],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1178 : RecordDataValid section14Catalog 13 (⟨55,(10),[1,2,5,6,13,14],[190],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1179 : RecordDataValid section14Catalog 13 (⟨55,(10),[1,2,5,6,13,14],[170,174],97⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨97,[1,2,5,6,9,10,13,14],97⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1180 : RecordDataValid section14Catalog 13 (⟨55,(10),[1,5,13],[186],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1181 : RecordDataValid section14Catalog 13 (⟨55,(11),[1,2,5,6,13,14],[170,174],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1182 : RecordDataValid section14Catalog 13 (⟨55,(11),[1,2,5,6,13,14],[190],234⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨234,[1,2,5,6,9,10,13,14],234⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1183 : RecordDataValid section14Catalog 13 (⟨55,(11),[1,5,13],[186],234⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨234,[1,2,5,6,9,10,13,14],234⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_1152_1184 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1152).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1152).take 32 = [⟨47,(24),[1,2,5,6,13,14],[190],324⟩,⟨47,(24),[1,5,13],[186],324⟩,⟨55,(0),[1,5,6,13,14],[190],3⟩,⟨55,(0),[1,5,13],[186],3⟩,⟨55,(0),[2,6,13,14],[170,174],97⟩,⟨55,(1),[1,5,6,13,14],[170,174,190],3⟩,⟨55,(1),[1,5,13],[186],3⟩,⟨55,(2),[6,13],[190],2⟩,⟨55,(2),[13],[170,174,186],2⟩,⟨55,(3),[1,6,13],[170,174],2⟩,⟨55,(3),[13],[186,190],2⟩,⟨55,(4),[1,5,6,13,14],[170,174,190],3⟩,⟨55,(4),[1,5,13],[186],3⟩,⟨55,(5),[1,5,6,13,14],[170,174,190],3⟩,⟨55,(5),[1,5,13],[186],3⟩,⟨55,(6),[1,2,5,6,13,14],[170,174],2⟩,⟨55,(6),[6,13],[190],2⟩,⟨55,(6),[13],[186],2⟩,⟨55,(7),[1,2,5,6,13,14],[190],2⟩,⟨55,(7),[1,5,13],[186],2⟩,⟨55,(7),[1,6,13],[170,174],2⟩,⟨55,(8),[1,2,5,6,13,14],[190],3⟩,⟨55,(8),[1,5,13],[186],3⟩,⟨55,(8),[5,6,13,14],[170,174],97⟩,⟨55,(9),[1,2,5,6,13,14],[170,174,190],3⟩,⟨55,(9),[1,5,13],[186],3⟩,⟨55,(10),[1,2,5,6,13,14],[190],29⟩,⟨55,(10),[1,2,5,6,13,14],[170,174],97⟩,⟨55,(10),[1,5,13],[186],29⟩,⟨55,(11),[1,2,5,6,13,14],[170,174],29⟩,⟨55,(11),[1,2,5,6,13,14],[190],234⟩,⟨55,(11),[1,5,13],[186],234⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1152
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1153
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1154
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1155
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1156
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1157
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1158
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1159
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1160
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1161
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1162
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1163
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1164
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1165
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1166
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1167
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1168
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1169
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1170
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1171
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1172
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1173
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1174
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1175
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1176
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1177
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1178
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1179
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1180
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1181
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1182
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1183
end Section14Records_13_1152_1184

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_1152_1184


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_1184_1216
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_1184_1216
private theorem valid1184 : RecordDataValid section14Catalog 13 (⟨55,(12),[5,6,13],[170,174,190],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1185 : RecordDataValid section14Catalog 13 (⟨55,(12),[5,13],[186],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1186 : RecordDataValid section14Catalog 13 (⟨55,(13),[5,6,13],[170,174,190],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1187 : RecordDataValid section14Catalog 13 (⟨55,(13),[5,13],[186],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1188 : RecordDataValid section14Catalog 13 (⟨55,(14),[1,2,5,6,13],[190],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1189 : RecordDataValid section14Catalog 13 (⟨55,(14),[1,2,5,6,13,14],[170,174],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1190 : RecordDataValid section14Catalog 13 (⟨55,(14),[1,5,13],[186],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1191 : RecordDataValid section14Catalog 13 (⟨55,(15),[1,2,5,6,13],[170,174],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1192 : RecordDataValid section14Catalog 13 (⟨55,(15),[1,2,5,6,13,14],[190],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1193 : RecordDataValid section14Catalog 13 (⟨55,(15),[1,5,13],[186],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1194 : RecordDataValid section14Catalog 13 (⟨58,(5),[13],[170,174,186,190],105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨105,[1,2,3,5,6,7,13,14,15],105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1195 : RecordDataValid section14Catalog 13 (⟨58,(7),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1196 : RecordDataValid section14Catalog 13 (⟨58,(7),[1,5,13],[186],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1197 : RecordDataValid section14Catalog 13 (⟨58,(7),[5,13],[174,190],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1198 : RecordDataValid section14Catalog 13 (⟨58,(8),[1,2,5,6,13,14],[174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1199 : RecordDataValid section14Catalog 13 (⟨58,(8),[5,13],[170,186],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1200 : RecordDataValid section14Catalog 13 (⟨58,(9),[5,6,13,14],[170,174,190],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1201 : RecordDataValid section14Catalog 13 (⟨58,(9),[5,13],[186],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1202 : RecordDataValid section14Catalog 13 (⟨58,(15),[1,2,5,6,13,14],[174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1203 : RecordDataValid section14Catalog 13 (⟨58,(15),[5,13],[170,186],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1204 : RecordDataValid section14Catalog 13 (⟨58,(16),[1,2,5,6,13,14],[174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1205 : RecordDataValid section14Catalog 13 (⟨58,(16),[5,13],[170,186],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1206 : RecordDataValid section14Catalog 13 (⟨58,(17),[1,2,5,6,13,14],[170,174,190],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1207 : RecordDataValid section14Catalog 13 (⟨58,(17),[1,5,13],[186],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1208 : RecordDataValid section14Catalog 13 (⟨58,(19),[1,2,5,6,13,14],[174,190],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1209 : RecordDataValid section14Catalog 13 (⟨58,(19),[1,13],[170,186],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1210 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨341,[1,2,3,5,6,7,9,10,11,13,14,15],342⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1211 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1212 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,2,5,6,9,10,13,14],[5],341⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨341,[1,2,3,5,6,7,9,10,11,13,14,15],342⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1213 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1214 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1215 : RecordDataValid section14Catalog 13 (⟨60,(-1),[1,2,5,6,13,14],[41,57],60⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨60,[1,2,3,5,6,7,13,14,15],60⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_1184_1216 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1184).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1184).take 32 = [⟨55,(12),[5,6,13],[170,174,190],99⟩,⟨55,(12),[5,13],[186],99⟩,⟨55,(13),[5,6,13],[170,174,190],99⟩,⟨55,(13),[5,13],[186],99⟩,⟨55,(14),[1,2,5,6,13],[190],99⟩,⟨55,(14),[1,2,5,6,13,14],[170,174],99⟩,⟨55,(14),[1,5,13],[186],99⟩,⟨55,(15),[1,2,5,6,13],[170,174],99⟩,⟨55,(15),[1,2,5,6,13,14],[190],99⟩,⟨55,(15),[1,5,13],[186],99⟩,⟨58,(5),[13],[170,174,186,190],105⟩,⟨58,(7),[1,2,5,6,13,14],[170],3⟩,⟨58,(7),[1,5,13],[186],3⟩,⟨58,(7),[5,13],[174,190],48⟩,⟨58,(8),[1,2,5,6,13,14],[174,190],3⟩,⟨58,(8),[5,13],[170,186],48⟩,⟨58,(9),[5,6,13,14],[170,174,190],143⟩,⟨58,(9),[5,13],[186],143⟩,⟨58,(15),[1,2,5,6,13,14],[174,190],3⟩,⟨58,(15),[5,13],[170,186],48⟩,⟨58,(16),[1,2,5,6,13,14],[174,190],3⟩,⟨58,(16),[5,13],[170,186],48⟩,⟨58,(17),[1,2,5,6,13,14],[170,174,190],48⟩,⟨58,(17),[1,5,13],[186],48⟩,⟨58,(19),[1,2,5,6,13,14],[174,190],143⟩,⟨58,(19),[1,13],[170,186],48⟩,⟨60,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],341⟩,⟨60,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩,⟨60,(-1),[1,2,5,6,9,10,13,14],[5],341⟩,⟨60,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩,⟨60,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩,⟨60,(-1),[1,2,5,6,13,14],[41,57],60⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1184
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1185
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1186
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1187
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1188
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1189
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1190
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1191
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1192
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1193
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1194
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1195
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1196
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1197
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1198
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1199
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1200
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1201
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1202
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1203
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1204
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1205
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1206
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1207
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1208
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1209
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1210
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1211
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1212
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1213
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1214
  · exact recordValid_of_data section14Catalog 13 _ hnum valid1215
end Section14Records_13_1184_1216

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_1184_1216

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 1088).take 128, section14RecordValid section14Catalog 13 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (13 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 13 r
  exact (all_of_interval_split P xs 1088 1152 1216 (by decide) (by decide) (all_of_interval_split P xs 1088 1120 1152 (by decide) (by decide) (Freiman.workReverse20260919_s0013_records_1088_1120 hnum) (Freiman.workReverse20260919_s0013_records_1120_1152 hnum)) (all_of_interval_split P xs 1152 1184 1216 (by decide) (by decide) (Freiman.workReverse20260919_s0013_records_1152_1184 hnum) (Freiman.workReverse20260919_s0013_records_1184_1216 hnum)))

#print axioms solution
