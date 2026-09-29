-- Prove2me | solution 1 for Freiman.section14_s0002_records_1056_1088
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T06:14:56.611107+00:00
-- url     : https://prove2.me/submissions/ed7bb5f4-853e-402b-8d3e-91d4355479bf

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
namespace Section14Records_2_1056_1088
private theorem valid1056 : RecordDataValid section14Catalog 2 (⟨42,(11),[1,2,5,6,13,14],[170],257⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨257,[1,2,3,4,5,6,7,8,13,14,15,16],258⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1057 : RecordDataValid section14Catalog 2 (⟨42,(11),[1,2,5,6,13,14],[174],292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨292,[1,2,3,5,6,7,13,14,15],293⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1058 : RecordDataValid section14Catalog 2 (⟨42,(11),[1,2,5,6,13,14],[190],316⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨316,[1,2,4,5,6,8,13,14,16],317⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1059 : RecordDataValid section14Catalog 2 (⟨42,(12),[1,2,5,6,13,14],[170],257⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨257,[1,2,3,4,5,6,7,8,13,14,15,16],258⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1060 : RecordDataValid section14Catalog 2 (⟨42,(12),[1,2,5,6,13,14],[174],292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨292,[1,2,3,5,6,7,13,14,15],293⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1061 : RecordDataValid section14Catalog 2 (⟨42,(12),[1,2,5,6,13,14],[190],316⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨316,[1,2,4,5,6,8,13,14,16],317⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1062 : RecordDataValid section14Catalog 2 (⟨42,(13),[1,2,5,6,13,14],[170],257⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨257,[1,2,3,4,5,6,7,8,13,14,15,16],258⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1063 : RecordDataValid section14Catalog 2 (⟨42,(13),[1,2,5,6,13,14],[174],292⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨292,[1,2,3,5,6,7,13,14,15],293⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1064 : RecordDataValid section14Catalog 2 (⟨42,(13),[1,2,5,6,13,14],[190],316⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨316,[1,2,4,5,6,8,13,14,16],317⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1065 : RecordDataValid section14Catalog 2 (⟨42,(14),[1,2,5,6,13,14],[170],256⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨256,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],257⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1066 : RecordDataValid section14Catalog 2 (⟨42,(14),[1,2,5,6,13,14],[174],291⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨291,[1,2,3,5,6,7,13,14,15],292⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1067 : RecordDataValid section14Catalog 2 (⟨42,(14),[1,2,5,6,13,14],[190],315⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨315,[1,2,4,5,6,8,9,10,12,13,14,16],316⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1068 : RecordDataValid section14Catalog 2 (⟨42,(15),[1,2,5,6,13,14],[170],258⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨258,[1,2,3,4,5,6,7,8,13,14,15,16],259⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1069 : RecordDataValid section14Catalog 2 (⟨42,(15),[1,2,5,6,13,14],[174],293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨293,[1,2,3,5,6,7,13,14,15],294⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1070 : RecordDataValid section14Catalog 2 (⟨42,(15),[1,2,5,6,13,14],[190],317⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨317,[1,2,4,5,6,8,13,14,16],318⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1071 : RecordDataValid section14Catalog 2 (⟨42,(16),[1,2,5,6,13,14],[170],258⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨258,[1,2,3,4,5,6,7,8,13,14,15,16],259⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1072 : RecordDataValid section14Catalog 2 (⟨42,(16),[1,2,5,6,13,14],[174],293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨293,[1,2,3,5,6,7,13,14,15],294⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1073 : RecordDataValid section14Catalog 2 (⟨42,(16),[1,2,5,6,13,14],[190],317⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨317,[1,2,4,5,6,8,13,14,16],318⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1074 : RecordDataValid section14Catalog 2 (⟨42,(17),[1,2,5,6,13,14],[170],258⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨258,[1,2,3,4,5,6,7,8,13,14,15,16],259⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1075 : RecordDataValid section14Catalog 2 (⟨42,(17),[1,2,5,6,13,14],[174],293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨293,[1,2,3,5,6,7,13,14,15],294⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1076 : RecordDataValid section14Catalog 2 (⟨42,(17),[1,2,5,6,13,14],[190],317⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨317,[1,2,4,5,6,8,13,14,16],318⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1077 : RecordDataValid section14Catalog 2 (⟨42,(18),[1,2,5,6,13,14],[170],258⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨258,[1,2,3,4,5,6,7,8,13,14,15,16],259⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1078 : RecordDataValid section14Catalog 2 (⟨42,(18),[1,2,5,6,13,14],[174],293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨293,[1,2,3,5,6,7,13,14,15],294⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1079 : RecordDataValid section14Catalog 2 (⟨42,(18),[1,2,5,6,13,14],[190],317⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨317,[1,2,4,5,6,8,13,14,16],318⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1080 : RecordDataValid section14Catalog 2 (⟨42,(19),[1,2,5,6,13,14],[170],258⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨258,[1,2,3,4,5,6,7,8,13,14,15,16],259⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1081 : RecordDataValid section14Catalog 2 (⟨42,(19),[1,2,5,6,13,14],[174],293⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨293,[1,2,3,5,6,7,13,14,15],294⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1082 : RecordDataValid section14Catalog 2 (⟨42,(19),[1,2,5,6,13,14],[190],317⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨317,[1,2,4,5,6,8,13,14,16],318⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1083 : RecordDataValid section14Catalog 2 (⟨42,(20),[1,2,5,6,13,14],[170],259⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨259,[1,2,3,4,5,6,7,8,13,14,15,16],260⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1084 : RecordDataValid section14Catalog 2 (⟨42,(20),[1,2,5,6,13,14],[174],294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨294,[1,2,3,5,6,7,13,14,15],295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1085 : RecordDataValid section14Catalog 2 (⟨42,(20),[1,2,5,6,13,14],[190],318⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨318,[1,2,4,5,6,8,13,14,16],319⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1086 : RecordDataValid section14Catalog 2 (⟨42,(21),[1,2,5,6,13,14],[170],259⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨259,[1,2,3,4,5,6,7,8,13,14,15,16],260⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1087 : RecordDataValid section14Catalog 2 (⟨42,(21),[1,2,5,6,13,14],[174],294⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨294,[1,2,3,5,6,7,13,14,15],295⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 1056).take 32, section14RecordValid section14Catalog 2 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 1056).take 32 = [⟨42,(11),[1,2,5,6,13,14],[170],257⟩,⟨42,(11),[1,2,5,6,13,14],[174],292⟩,⟨42,(11),[1,2,5,6,13,14],[190],316⟩,⟨42,(12),[1,2,5,6,13,14],[170],257⟩,⟨42,(12),[1,2,5,6,13,14],[174],292⟩,⟨42,(12),[1,2,5,6,13,14],[190],316⟩,⟨42,(13),[1,2,5,6,13,14],[170],257⟩,⟨42,(13),[1,2,5,6,13,14],[174],292⟩,⟨42,(13),[1,2,5,6,13,14],[190],316⟩,⟨42,(14),[1,2,5,6,13,14],[170],256⟩,⟨42,(14),[1,2,5,6,13,14],[174],291⟩,⟨42,(14),[1,2,5,6,13,14],[190],315⟩,⟨42,(15),[1,2,5,6,13,14],[170],258⟩,⟨42,(15),[1,2,5,6,13,14],[174],293⟩,⟨42,(15),[1,2,5,6,13,14],[190],317⟩,⟨42,(16),[1,2,5,6,13,14],[170],258⟩,⟨42,(16),[1,2,5,6,13,14],[174],293⟩,⟨42,(16),[1,2,5,6,13,14],[190],317⟩,⟨42,(17),[1,2,5,6,13,14],[170],258⟩,⟨42,(17),[1,2,5,6,13,14],[174],293⟩,⟨42,(17),[1,2,5,6,13,14],[190],317⟩,⟨42,(18),[1,2,5,6,13,14],[170],258⟩,⟨42,(18),[1,2,5,6,13,14],[174],293⟩,⟨42,(18),[1,2,5,6,13,14],[190],317⟩,⟨42,(19),[1,2,5,6,13,14],[170],258⟩,⟨42,(19),[1,2,5,6,13,14],[174],293⟩,⟨42,(19),[1,2,5,6,13,14],[190],317⟩,⟨42,(20),[1,2,5,6,13,14],[170],259⟩,⟨42,(20),[1,2,5,6,13,14],[174],294⟩,⟨42,(20),[1,2,5,6,13,14],[190],318⟩,⟨42,(21),[1,2,5,6,13,14],[170],259⟩,⟨42,(21),[1,2,5,6,13,14],[174],294⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1056
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1057
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1058
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1059
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1060
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1061
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1062
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1063
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1064
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1065
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1066
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1067
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1068
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1069
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1070
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1071
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1072
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1073
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1074
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1075
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1076
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1077
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1078
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1079
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1080
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1081
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1082
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1083
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1084
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1085
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1086
  · exact recordValid_of_data section14Catalog 2 _ hnum valid1087
end Section14Records_2_1056_1088

#print axioms solution
