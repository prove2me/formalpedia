-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_3104_3136
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:44:44.927292+00:00
-- url     : https://prove2.me/submissions/0bf1bac1-be40-49f1-8376-f57f6a02324f

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
namespace Section14Records_6_3104_3136
private theorem valid3104 : RecordDataValid section14Catalog 6 (⟨213,(15),[5,6],[174],1035⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1035,[3,5,6,7],1039⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3105 : RecordDataValid section14Catalog 6 (⟨215,(0),[1,2,5,6],[170],728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨728,[1,2,4,5,6,8,9,10,12],729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3106 : RecordDataValid section14Catalog 6 (⟨215,(0),[5,6],[174],728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨728,[1,2,4,5,6,8,9,10,12],729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3107 : RecordDataValid section14Catalog 6 (⟨215,(1),[1,2,5,6],[170],729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨729,[1,2,4,5,6,8,9,10,12],730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3108 : RecordDataValid section14Catalog 6 (⟨215,(1),[5,6],[174],729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨729,[1,2,4,5,6,8,9,10,12],730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3109 : RecordDataValid section14Catalog 6 (⟨215,(2),[1,2,5,6],[170],730⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨730,[1,2,4,5,6,8,9,10,12],731⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3110 : RecordDataValid section14Catalog 6 (⟨215,(2),[5,6],[174],730⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨730,[1,2,4,5,6,8,9,10,12],731⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3111 : RecordDataValid section14Catalog 6 (⟨215,(3),[1,2,5,6],[170],731⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨731,[1,2,4,5,6,8,9,10,12],732⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3112 : RecordDataValid section14Catalog 6 (⟨215,(3),[5,6],[174],731⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨731,[1,2,4,5,6,8,9,10,12],732⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3113 : RecordDataValid section14Catalog 6 (⟨215,(4),[1,2,5,6],[170],728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨728,[1,2,4,5,6,8,9,10,12],729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3114 : RecordDataValid section14Catalog 6 (⟨215,(4),[5,6],[174],728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨728,[1,2,4,5,6,8,9,10,12],729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3115 : RecordDataValid section14Catalog 6 (⟨215,(5),[1,2,5,6],[170],729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨729,[1,2,4,5,6,8,9,10,12],730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3116 : RecordDataValid section14Catalog 6 (⟨215,(5),[5,6],[174],729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨729,[1,2,4,5,6,8,9,10,12],730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3117 : RecordDataValid section14Catalog 6 (⟨215,(6),[1,2,5,6],[170],732⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨732,[1,2,4,5,6,8,9,10,12],733⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3118 : RecordDataValid section14Catalog 6 (⟨215,(6),[5,6],[174],732⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨732,[1,2,4,5,6,8,9,10,12],733⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3119 : RecordDataValid section14Catalog 6 (⟨215,(7),[1,2,5,6],[170],731⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨731,[1,2,4,5,6,8,9,10,12],732⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3120 : RecordDataValid section14Catalog 6 (⟨215,(7),[5,6],[174],731⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨731,[1,2,4,5,6,8,9,10,12],732⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3121 : RecordDataValid section14Catalog 6 (⟨215,(8),[1,2,5,6],[170],728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨728,[1,2,4,5,6,8,9,10,12],729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3122 : RecordDataValid section14Catalog 6 (⟨215,(8),[5,6],[174],728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨728,[1,2,4,5,6,8,9,10,12],729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3123 : RecordDataValid section14Catalog 6 (⟨215,(9),[1,2,5,6],[170],729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨729,[1,2,4,5,6,8,9,10,12],730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3124 : RecordDataValid section14Catalog 6 (⟨215,(9),[5,6],[174],729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨729,[1,2,4,5,6,8,9,10,12],730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3125 : RecordDataValid section14Catalog 6 (⟨215,(10),[1,2,5,6],[170],730⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨730,[1,2,4,5,6,8,9,10,12],731⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3126 : RecordDataValid section14Catalog 6 (⟨215,(10),[5,6],[174],730⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨730,[1,2,4,5,6,8,9,10,12],731⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3127 : RecordDataValid section14Catalog 6 (⟨215,(11),[1,2,5,6],[170],731⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨731,[1,2,4,5,6,8,9,10,12],732⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3128 : RecordDataValid section14Catalog 6 (⟨215,(11),[5,6],[174],731⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨731,[1,2,4,5,6,8,9,10,12],732⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3129 : RecordDataValid section14Catalog 6 (⟨215,(12),[1,2,5,6],[170],728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨728,[1,2,4,5,6,8,9,10,12],729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3130 : RecordDataValid section14Catalog 6 (⟨215,(12),[5,6],[174],728⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨728,[1,2,4,5,6,8,9,10,12],729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3131 : RecordDataValid section14Catalog 6 (⟨215,(13),[1,2,5,6],[170],729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨729,[1,2,4,5,6,8,9,10,12],730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3132 : RecordDataValid section14Catalog 6 (⟨215,(13),[5,6],[174],729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨729,[1,2,4,5,6,8,9,10,12],730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3133 : RecordDataValid section14Catalog 6 (⟨215,(14),[1,2,5,6],[170],733⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨733,[1,2,4,5,6,8,9,10,12],734⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3134 : RecordDataValid section14Catalog 6 (⟨215,(14),[5,6],[174],733⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨733,[1,2,4,5,6,8,9,10,12],734⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3135 : RecordDataValid section14Catalog 6 (⟨215,(15),[1,2,5,6],[170],731⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨731,[1,2,4,5,6,8,9,10,12],732⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3104).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3104).take 32 = [⟨213,(15),[5,6],[174],1035⟩,⟨215,(0),[1,2,5,6],[170],728⟩,⟨215,(0),[5,6],[174],728⟩,⟨215,(1),[1,2,5,6],[170],729⟩,⟨215,(1),[5,6],[174],729⟩,⟨215,(2),[1,2,5,6],[170],730⟩,⟨215,(2),[5,6],[174],730⟩,⟨215,(3),[1,2,5,6],[170],731⟩,⟨215,(3),[5,6],[174],731⟩,⟨215,(4),[1,2,5,6],[170],728⟩,⟨215,(4),[5,6],[174],728⟩,⟨215,(5),[1,2,5,6],[170],729⟩,⟨215,(5),[5,6],[174],729⟩,⟨215,(6),[1,2,5,6],[170],732⟩,⟨215,(6),[5,6],[174],732⟩,⟨215,(7),[1,2,5,6],[170],731⟩,⟨215,(7),[5,6],[174],731⟩,⟨215,(8),[1,2,5,6],[170],728⟩,⟨215,(8),[5,6],[174],728⟩,⟨215,(9),[1,2,5,6],[170],729⟩,⟨215,(9),[5,6],[174],729⟩,⟨215,(10),[1,2,5,6],[170],730⟩,⟨215,(10),[5,6],[174],730⟩,⟨215,(11),[1,2,5,6],[170],731⟩,⟨215,(11),[5,6],[174],731⟩,⟨215,(12),[1,2,5,6],[170],728⟩,⟨215,(12),[5,6],[174],728⟩,⟨215,(13),[1,2,5,6],[170],729⟩,⟨215,(13),[5,6],[174],729⟩,⟨215,(14),[1,2,5,6],[170],733⟩,⟨215,(14),[5,6],[174],733⟩,⟨215,(15),[1,2,5,6],[170],731⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3104
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3105
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3106
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3107
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3108
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3109
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3110
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3111
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3112
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3113
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3114
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3115
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3116
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3117
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3118
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3119
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3120
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3121
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3122
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3123
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3124
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3125
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3126
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3127
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3128
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3129
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3130
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3131
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3132
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3133
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3134
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3135
end Section14Records_6_3104_3136

#print axioms solution
