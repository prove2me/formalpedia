-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_3296_3328
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:59:24.200652+00:00
-- url     : https://prove2.me/submissions/b229e992-6491-4ff3-8b45-bdac46f2060b

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
namespace Section14Records_5_3296_3328
private theorem valid3296 : RecordDataValid section14Catalog 5 (⟨207,(7),[1,2,5,6,13,14],[170],481⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3297 : RecordDataValid section14Catalog 5 (⟨207,(7),[5,6],[174],1022⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1022,[3,5,6,7],1026⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3298 : RecordDataValid section14Catalog 5 (⟨207,(8),[1,2,5,6,13,14],[170],483⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨483,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],484⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3299 : RecordDataValid section14Catalog 5 (⟨207,(8),[5,6],[174],1024⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1024,[3,5,6,7],1028⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3300 : RecordDataValid section14Catalog 5 (⟨207,(9),[1,2,5,6,13,14],[170],484⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨484,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],485⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3301 : RecordDataValid section14Catalog 5 (⟨207,(9),[5,6],[174],1025⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1025,[3,5,6,7],1029⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3302 : RecordDataValid section14Catalog 5 (⟨207,(10),[1,2,5,6,13,14],[170],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3303 : RecordDataValid section14Catalog 5 (⟨207,(10),[5,6],[174],1026⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1026,[3,5,6,7],1030⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3304 : RecordDataValid section14Catalog 5 (⟨207,(11),[1,2,5,6,13,14],[170],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3305 : RecordDataValid section14Catalog 5 (⟨207,(11),[5,6],[174],1026⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1026,[3,5,6,7],1030⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3306 : RecordDataValid section14Catalog 5 (⟨207,(12),[1,2,5,6,13,14],[170],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3307 : RecordDataValid section14Catalog 5 (⟨207,(12),[5,6],[174],1026⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1026,[3,5,6,7],1030⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3308 : RecordDataValid section14Catalog 5 (⟨207,(13),[1,2,5,6,13,14],[170],485⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3309 : RecordDataValid section14Catalog 5 (⟨207,(13),[5,6],[174],1026⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1026,[3,5,6,7],1030⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3310 : RecordDataValid section14Catalog 5 (⟨207,(14),[1,2,5,6,13,14],[170],484⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨484,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],485⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3311 : RecordDataValid section14Catalog 5 (⟨207,(14),[5,6],[174],1025⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1025,[3,5,6,7],1029⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3312 : RecordDataValid section14Catalog 5 (⟨207,(15),[1,2,5,6,13,14],[170],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3313 : RecordDataValid section14Catalog 5 (⟨207,(15),[5,6],[174],1027⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1027,[3,5,6,7],1031⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3314 : RecordDataValid section14Catalog 5 (⟨207,(16),[1,2,5,6,13,14],[170],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3315 : RecordDataValid section14Catalog 5 (⟨207,(16),[5,6],[174],1027⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1027,[3,5,6,7],1031⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3316 : RecordDataValid section14Catalog 5 (⟨207,(17),[1,2,5,6,13,14],[170],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3317 : RecordDataValid section14Catalog 5 (⟨207,(17),[5,6],[174],1027⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1027,[3,5,6,7],1031⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3318 : RecordDataValid section14Catalog 5 (⟨207,(18),[1,2,5,6,13,14],[170],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3319 : RecordDataValid section14Catalog 5 (⟨207,(18),[5,6],[174],1027⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1027,[3,5,6,7],1031⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3320 : RecordDataValid section14Catalog 5 (⟨207,(19),[1,2,5,6,13,14],[170],486⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3321 : RecordDataValid section14Catalog 5 (⟨207,(19),[5,6],[174],1027⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1027,[3,5,6,7],1031⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3322 : RecordDataValid section14Catalog 5 (⟨207,(20),[1,2,5,6,13,14],[170],487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨487,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],488⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3323 : RecordDataValid section14Catalog 5 (⟨207,(20),[5,6],[174],1028⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1028,[3,5,6,7],1032⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3324 : RecordDataValid section14Catalog 5 (⟨207,(21),[1,2,5,6,13,14],[170],487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨487,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],488⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3325 : RecordDataValid section14Catalog 5 (⟨207,(21),[5,6],[174],1028⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1028,[3,5,6,7],1032⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3326 : RecordDataValid section14Catalog 5 (⟨207,(22),[1,2,5,6,13,14],[170],487⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨487,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],488⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3327 : RecordDataValid section14Catalog 5 (⟨207,(22),[5,6],[174],1028⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1028,[3,5,6,7],1032⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3296).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3296).take 32 = [⟨207,(7),[1,2,5,6,13,14],[170],481⟩,⟨207,(7),[5,6],[174],1022⟩,⟨207,(8),[1,2,5,6,13,14],[170],483⟩,⟨207,(8),[5,6],[174],1024⟩,⟨207,(9),[1,2,5,6,13,14],[170],484⟩,⟨207,(9),[5,6],[174],1025⟩,⟨207,(10),[1,2,5,6,13,14],[170],485⟩,⟨207,(10),[5,6],[174],1026⟩,⟨207,(11),[1,2,5,6,13,14],[170],485⟩,⟨207,(11),[5,6],[174],1026⟩,⟨207,(12),[1,2,5,6,13,14],[170],485⟩,⟨207,(12),[5,6],[174],1026⟩,⟨207,(13),[1,2,5,6,13,14],[170],485⟩,⟨207,(13),[5,6],[174],1026⟩,⟨207,(14),[1,2,5,6,13,14],[170],484⟩,⟨207,(14),[5,6],[174],1025⟩,⟨207,(15),[1,2,5,6,13,14],[170],486⟩,⟨207,(15),[5,6],[174],1027⟩,⟨207,(16),[1,2,5,6,13,14],[170],486⟩,⟨207,(16),[5,6],[174],1027⟩,⟨207,(17),[1,2,5,6,13,14],[170],486⟩,⟨207,(17),[5,6],[174],1027⟩,⟨207,(18),[1,2,5,6,13,14],[170],486⟩,⟨207,(18),[5,6],[174],1027⟩,⟨207,(19),[1,2,5,6,13,14],[170],486⟩,⟨207,(19),[5,6],[174],1027⟩,⟨207,(20),[1,2,5,6,13,14],[170],487⟩,⟨207,(20),[5,6],[174],1028⟩,⟨207,(21),[1,2,5,6,13,14],[170],487⟩,⟨207,(21),[5,6],[174],1028⟩,⟨207,(22),[1,2,5,6,13,14],[170],487⟩,⟨207,(22),[5,6],[174],1028⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3296
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3297
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3298
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3299
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3300
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3301
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3302
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3303
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3304
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3305
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3306
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3307
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3308
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3309
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3310
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3311
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3312
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3313
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3314
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3315
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3316
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3317
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3318
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3319
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3320
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3321
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3322
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3323
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3324
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3325
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3326
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3327
end Section14Records_5_3296_3328

#print axioms solution
