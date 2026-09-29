-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_4224_4256
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:08:49.660317+00:00
-- url     : https://prove2.me/submissions/c869e169-e94c-4bf0-bad7-7f0ec56a8175

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
namespace Section14Records_5_4224_4256
private theorem valid4224 : RecordDataValid section14Catalog 5 (⟨255,(8),[1,2,5,6],[170],901⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨901,[1,2,4,5,6,8,9,10,12],903⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4225 : RecordDataValid section14Catalog 5 (⟨255,(9),[1,2,5,6],[170],902⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨902,[1,2,4,5,6,8,9,10,12],904⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4226 : RecordDataValid section14Catalog 5 (⟨255,(10),[1,2,5,6],[170],899⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨899,[1,2,4,5,6,8],901⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4227 : RecordDataValid section14Catalog 5 (⟨255,(11),[1,2,5,6],[170],899⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨899,[1,2,4,5,6,8],901⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4228 : RecordDataValid section14Catalog 5 (⟨255,(12),[1,2,5,6],[170],900⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨900,[1,2,4,5,6,8,9,10,12],902⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4229 : RecordDataValid section14Catalog 5 (⟨255,(13),[1,2,5,6],[170],901⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨901,[1,2,4,5,6,8,9,10,12],903⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4230 : RecordDataValid section14Catalog 5 (⟨255,(14),[1,2,5,6],[170],902⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨902,[1,2,4,5,6,8,9,10,12],904⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4231 : RecordDataValid section14Catalog 5 (⟨255,(15),[1,2,5,6],[170],904⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨904,[1,2,4,5,6,8,9,10,12],906⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4232 : RecordDataValid section14Catalog 5 (⟨255,(16),[1,2,5,6],[170],904⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨904,[1,2,4,5,6,8,9,10,12],906⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4233 : RecordDataValid section14Catalog 5 (⟨255,(17),[1,2,5,6],[170],900⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨900,[1,2,4,5,6,8,9,10,12],902⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4234 : RecordDataValid section14Catalog 5 (⟨255,(18),[1,2,5,6],[170],901⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨901,[1,2,4,5,6,8,9,10,12],903⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4235 : RecordDataValid section14Catalog 5 (⟨255,(19),[1,2,5,6],[170],902⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨902,[1,2,4,5,6,8,9,10,12],904⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4236 : RecordDataValid section14Catalog 5 (⟨255,(20),[1,2,5,6],[170],905⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨905,[1,2,4,5,6,8,9,10,12,13,14,16],907⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4237 : RecordDataValid section14Catalog 5 (⟨255,(21),[1,2,5,6],[170],905⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨905,[1,2,4,5,6,8,9,10,12,13,14,16],907⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4238 : RecordDataValid section14Catalog 5 (⟨255,(22),[1,2,5,6],[170],905⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨905,[1,2,4,5,6,8,9,10,12,13,14,16],907⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4239 : RecordDataValid section14Catalog 5 (⟨255,(23),[1,2,5,6],[170],901⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨901,[1,2,4,5,6,8,9,10,12],903⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4240 : RecordDataValid section14Catalog 5 (⟨255,(24),[1,2,5,6],[170],902⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨902,[1,2,4,5,6,8,9,10,12],904⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4241 : RecordDataValid section14Catalog 5 (⟨258,(5),[1,2,5,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4242 : RecordDataValid section14Catalog 5 (⟨258,(7),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4243 : RecordDataValid section14Catalog 5 (⟨258,(8),[1,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4244 : RecordDataValid section14Catalog 5 (⟨258,(9),[5,6,13,14],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4245 : RecordDataValid section14Catalog 5 (⟨258,(15),[5,13],[170],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4246 : RecordDataValid section14Catalog 5 (⟨258,(16),[1,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4247 : RecordDataValid section14Catalog 5 (⟨258,(17),[1,2,5,6,13,14],[170],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4248 : RecordDataValid section14Catalog 5 (⟨258,(19),[2,5,6,14],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4249 : RecordDataValid section14Catalog 5 (⟨259,(1),[1,2,5,6],[170],906⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨906,[1,2,4,5,6,8,9,10,12],908⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4250 : RecordDataValid section14Catalog 5 (⟨259,(3),[1,2,5,6],[170],907⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨907,[1,2,4,5,6,8,9,10,12],909⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4251 : RecordDataValid section14Catalog 5 (⟨259,(5),[5,6],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4252 : RecordDataValid section14Catalog 5 (⟨259,(7),[5,6],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4253 : RecordDataValid section14Catalog 5 (⟨259,(11),[2,5,6],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4254 : RecordDataValid section14Catalog 5 (⟨259,(13),[5,6],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4255 : RecordDataValid section14Catalog 5 (⟨259,(15),[2,5],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4224).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4224).take 32 = [⟨255,(8),[1,2,5,6],[170],901⟩,⟨255,(9),[1,2,5,6],[170],902⟩,⟨255,(10),[1,2,5,6],[170],899⟩,⟨255,(11),[1,2,5,6],[170],899⟩,⟨255,(12),[1,2,5,6],[170],900⟩,⟨255,(13),[1,2,5,6],[170],901⟩,⟨255,(14),[1,2,5,6],[170],902⟩,⟨255,(15),[1,2,5,6],[170],904⟩,⟨255,(16),[1,2,5,6],[170],904⟩,⟨255,(17),[1,2,5,6],[170],900⟩,⟨255,(18),[1,2,5,6],[170],901⟩,⟨255,(19),[1,2,5,6],[170],902⟩,⟨255,(20),[1,2,5,6],[170],905⟩,⟨255,(21),[1,2,5,6],[170],905⟩,⟨255,(22),[1,2,5,6],[170],905⟩,⟨255,(23),[1,2,5,6],[170],901⟩,⟨255,(24),[1,2,5,6],[170],902⟩,⟨258,(5),[1,2,5,14],[170],3⟩,⟨258,(7),[1,2,5,6,13,14],[170],3⟩,⟨258,(8),[1,5,6,13,14],[170],3⟩,⟨258,(9),[5,6,13,14],[170],143⟩,⟨258,(15),[5,13],[170],48⟩,⟨258,(16),[1,5,6,13,14],[170],3⟩,⟨258,(17),[1,2,5,6,13,14],[170],48⟩,⟨258,(19),[2,5,6,14],[170],143⟩,⟨259,(1),[1,2,5,6],[170],906⟩,⟨259,(3),[1,2,5,6],[170],907⟩,⟨259,(5),[5,6],[170],143⟩,⟨259,(7),[5,6],[170],143⟩,⟨259,(11),[2,5,6],[170],143⟩,⟨259,(13),[5,6],[170],143⟩,⟨259,(15),[2,5],[170],143⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4224
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4225
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4226
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4227
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4228
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4229
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4230
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4231
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4232
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4233
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4234
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4235
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4236
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4237
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4238
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4239
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4240
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4241
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4242
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4243
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4244
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4245
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4246
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4247
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4248
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4249
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4250
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4251
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4252
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4253
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4254
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4255
end Section14Records_5_4224_4256

#print axioms solution
