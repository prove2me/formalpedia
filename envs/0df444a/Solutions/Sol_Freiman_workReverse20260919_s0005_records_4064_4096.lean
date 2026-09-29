-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_4064_4096
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:08:01.77636+00:00
-- url     : https://prove2.me/submissions/f58fc56d-05db-4425-a640-3a4d691903e4

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
namespace Section14Records_5_4064_4096
private theorem valid4064 : RecordDataValid section14Catalog 5 (⟨242,(5),[1,2,5,6],[170],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4065 : RecordDataValid section14Catalog 5 (⟨242,(5),[5,6],[174],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4066 : RecordDataValid section14Catalog 5 (⟨242,(6),[1,2,5,6],[170],872⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨872,[1,2,4,5,6,8,9,10,12,13,14,16],873⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4067 : RecordDataValid section14Catalog 5 (⟨242,(6),[5,6],[174],872⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨872,[1,2,4,5,6,8,9,10,12,13,14,16],873⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4068 : RecordDataValid section14Catalog 5 (⟨242,(7),[1,2,5,6],[170],874⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨874,[1,2,4,5,6,8,9,10,12],875⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4069 : RecordDataValid section14Catalog 5 (⟨242,(7),[5,6],[174],874⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨874,[1,2,4,5,6,8,9,10,12],875⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4070 : RecordDataValid section14Catalog 5 (⟨242,(8),[1,2,5,6],[170],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4071 : RecordDataValid section14Catalog 5 (⟨242,(8),[5,6],[174],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4072 : RecordDataValid section14Catalog 5 (⟨242,(9),[1,2,5,6],[170],874⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨874,[1,2,4,5,6,8,9,10,12],875⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4073 : RecordDataValid section14Catalog 5 (⟨242,(9),[5,6],[174],874⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨874,[1,2,4,5,6,8,9,10,12],875⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4074 : RecordDataValid section14Catalog 5 (⟨242,(10),[1,2,5,6],[170],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4075 : RecordDataValid section14Catalog 5 (⟨242,(10),[5,6],[174],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4076 : RecordDataValid section14Catalog 5 (⟨242,(11),[1,2,5,6],[170],872⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨872,[1,2,4,5,6,8,9,10,12,13,14,16],873⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4077 : RecordDataValid section14Catalog 5 (⟨242,(11),[5,6],[174],872⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨872,[1,2,4,5,6,8,9,10,12,13,14,16],873⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4078 : RecordDataValid section14Catalog 5 (⟨242,(12),[1,2,5,6],[170],875⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨875,[1,2,4,5,6,8,9,10,12],876⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4079 : RecordDataValid section14Catalog 5 (⟨242,(12),[5,6],[174],875⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨875,[1,2,4,5,6,8,9,10,12],876⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4080 : RecordDataValid section14Catalog 5 (⟨242,(13),[1,2,5,6],[170],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4081 : RecordDataValid section14Catalog 5 (⟨242,(13),[5,6],[174],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4082 : RecordDataValid section14Catalog 5 (⟨242,(14),[1,2,5,6],[170],875⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨875,[1,2,4,5,6,8,9,10,12],876⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4083 : RecordDataValid section14Catalog 5 (⟨242,(14),[5,6],[174],875⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨875,[1,2,4,5,6,8,9,10,12],876⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4084 : RecordDataValid section14Catalog 5 (⟨242,(15),[1,2,5,6],[170],625⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨625,[1,2,4,5,6,8,9,10,12],626⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4085 : RecordDataValid section14Catalog 5 (⟨242,(15),[5,6],[174],625⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨625,[1,2,4,5,6,8,9,10,12],626⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4086 : RecordDataValid section14Catalog 5 (⟨242,(16),[1,2,5,6],[170],626⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨626,[1,2,4,5,6,8,9,10,12],627⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4087 : RecordDataValid section14Catalog 5 (⟨242,(16),[5,6],[174],626⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨626,[1,2,4,5,6,8,9,10,12],627⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4088 : RecordDataValid section14Catalog 5 (⟨242,(17),[1,2,5,6],[170],286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨286,[1,2,4,5,6,8,9,10,12],287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4089 : RecordDataValid section14Catalog 5 (⟨242,(17),[5,6],[174],286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨286,[1,2,4,5,6,8,9,10,12],287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4090 : RecordDataValid section14Catalog 5 (⟨242,(18),[1,2,5,6],[170],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4091 : RecordDataValid section14Catalog 5 (⟨242,(18),[5,6],[174],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4092 : RecordDataValid section14Catalog 5 (⟨242,(19),[1,2,5,6],[170],286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨286,[1,2,4,5,6,8,9,10,12],287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4093 : RecordDataValid section14Catalog 5 (⟨242,(19),[5,6],[174],286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨286,[1,2,4,5,6,8,9,10,12],287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4094 : RecordDataValid section14Catalog 5 (⟨242,(20),[1,2,5,6],[170],876⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨876,[1,2,4,5,6,8,9,10,12],877⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4095 : RecordDataValid section14Catalog 5 (⟨242,(20),[5,6],[174],876⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨876,[1,2,4,5,6,8,9,10,12],877⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4064).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4064).take 32 = [⟨242,(5),[1,2,5,6],[170],632⟩,⟨242,(5),[5,6],[174],632⟩,⟨242,(6),[1,2,5,6],[170],872⟩,⟨242,(6),[5,6],[174],872⟩,⟨242,(7),[1,2,5,6],[170],874⟩,⟨242,(7),[5,6],[174],874⟩,⟨242,(8),[1,2,5,6],[170],101⟩,⟨242,(8),[5,6],[174],101⟩,⟨242,(9),[1,2,5,6],[170],874⟩,⟨242,(9),[5,6],[174],874⟩,⟨242,(10),[1,2,5,6],[170],632⟩,⟨242,(10),[5,6],[174],632⟩,⟨242,(11),[1,2,5,6],[170],872⟩,⟨242,(11),[5,6],[174],872⟩,⟨242,(12),[1,2,5,6],[170],875⟩,⟨242,(12),[5,6],[174],875⟩,⟨242,(13),[1,2,5,6],[170],101⟩,⟨242,(13),[5,6],[174],101⟩,⟨242,(14),[1,2,5,6],[170],875⟩,⟨242,(14),[5,6],[174],875⟩,⟨242,(15),[1,2,5,6],[170],625⟩,⟨242,(15),[5,6],[174],625⟩,⟨242,(16),[1,2,5,6],[170],626⟩,⟨242,(16),[5,6],[174],626⟩,⟨242,(17),[1,2,5,6],[170],286⟩,⟨242,(17),[5,6],[174],286⟩,⟨242,(18),[1,2,5,6],[170],101⟩,⟨242,(18),[5,6],[174],101⟩,⟨242,(19),[1,2,5,6],[170],286⟩,⟨242,(19),[5,6],[174],286⟩,⟨242,(20),[1,2,5,6],[170],876⟩,⟨242,(20),[5,6],[174],876⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4064
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4065
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4066
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4067
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4068
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4069
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4070
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4071
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4072
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4073
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4074
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4075
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4076
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4077
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4078
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4079
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4080
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4081
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4082
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4083
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4084
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4085
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4086
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4087
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4088
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4089
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4090
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4091
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4092
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4093
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4094
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4095
end Section14Records_5_4064_4096

#print axioms solution
