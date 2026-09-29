-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_4352_4416
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:39:45.8139+00:00
-- url     : https://prove2.me/submissions/69e1114c-3f04-4594-96c3-69ed86e488b1

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4352_4384
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_4352_4384
private theorem valid4352 : RecordDataValid section14Catalog 5 (⟨270,(8),[5],[170],1418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1418,[5,8,9,12],1423⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4353 : RecordDataValid section14Catalog 5 (⟨270,(9),[5],[170],1418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1418,[5,8,9,12],1423⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4354 : RecordDataValid section14Catalog 5 (⟨270,(10),[5],[170],1418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1418,[5,8,9,12],1423⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4355 : RecordDataValid section14Catalog 5 (⟨270,(11),[5],[170],1418⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1418,[5,8,9,12],1423⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4356 : RecordDataValid section14Catalog 5 (⟨270,(12),[5],[170],1419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1419,[5,8,9,12],1424⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4357 : RecordDataValid section14Catalog 5 (⟨270,(13),[5],[170],1419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1419,[5,8,9,12],1424⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4358 : RecordDataValid section14Catalog 5 (⟨270,(14),[5],[170],1419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1419,[5,8,9,12],1424⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4359 : RecordDataValid section14Catalog 5 (⟨270,(15),[5],[170],1419⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1419,[5,8,9,12],1424⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4360 : RecordDataValid section14Catalog 5 (⟨273,(0),[5],[170],1098⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1098,[3,5,7,8,9,11,12,15],1102⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4361 : RecordDataValid section14Catalog 5 (⟨273,(1),[5],[170],1099⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1099,[3,5,7,8,9,11,12,15],1103⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4362 : RecordDataValid section14Catalog 5 (⟨273,(2),[5],[170],1100⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1100,[3,5,7,8,9,11,12,15],1104⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4363 : RecordDataValid section14Catalog 5 (⟨273,(3),[5],[170],1100⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1100,[3,5,7,8,9,11,12,15],1104⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4364 : RecordDataValid section14Catalog 5 (⟨273,(4),[5],[170],1100⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1100,[3,5,7,8,9,11,12,15],1104⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4365 : RecordDataValid section14Catalog 5 (⟨273,(5),[5],[170],1098⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1098,[3,5,7,8,9,11,12,15],1102⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4366 : RecordDataValid section14Catalog 5 (⟨273,(6),[5],[170],1099⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1099,[3,5,7,8,9,11,12,15],1103⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4367 : RecordDataValid section14Catalog 5 (⟨273,(7),[5],[170],1101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1101,[3,5,7,8,9,11,12,15],1105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4368 : RecordDataValid section14Catalog 5 (⟨273,(8),[5],[170],1102⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1102,[3,5,7,8,9,11,12,15],1106⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4369 : RecordDataValid section14Catalog 5 (⟨273,(9),[5],[170],1101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1101,[3,5,7,8,9,11,12,15],1105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4370 : RecordDataValid section14Catalog 5 (⟨275,(0),[5],[170],1420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1420,[5,8,9,12],1425⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4371 : RecordDataValid section14Catalog 5 (⟨275,(1),[5],[170],1420⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1420,[5,8,9,12],1425⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4372 : RecordDataValid section14Catalog 5 (⟨275,(2),[5],[170],1421⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1421,[5,8,9,12],1426⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4373 : RecordDataValid section14Catalog 5 (⟨275,(3),[5],[170],1422⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1422,[5,8,9,12],1427⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4374 : RecordDataValid section14Catalog 5 (⟨275,(4),[5],[170],1423⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1423,[5,8,9,12],1428⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4375 : RecordDataValid section14Catalog 5 (⟨275,(5),[5],[170],1424⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1424,[5,8,9,12],1429⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4376 : RecordDataValid section14Catalog 5 (⟨275,(6),[5],[170],1424⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1424,[5,8,9,12],1429⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4377 : RecordDataValid section14Catalog 5 (⟨275,(7),[5],[170],1424⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1424,[5,8,9,12],1429⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4378 : RecordDataValid section14Catalog 5 (⟨275,(8),[5],[170],1422⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1422,[5,8,9,12],1427⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4379 : RecordDataValid section14Catalog 5 (⟨275,(9),[5],[170],1423⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1423,[5,8,9,12],1428⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4380 : RecordDataValid section14Catalog 5 (⟨278,(0),[5],[170],1108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1108,[3,5,7,8,9,11,12,15],1112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4381 : RecordDataValid section14Catalog 5 (⟨278,(1),[5],[170],1109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1109,[3,5,7,8,9,11,12,15],1113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4382 : RecordDataValid section14Catalog 5 (⟨278,(2),[5],[170],1110⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1110,[3,5,7,8,9,11,12,15],1114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4383 : RecordDataValid section14Catalog 5 (⟨278,(3),[5],[170],1110⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1110,[3,5,7,8,9,11,12,15],1114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_4352_4384 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4352).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4352).take 32 = [⟨270,(8),[5],[170],1418⟩,⟨270,(9),[5],[170],1418⟩,⟨270,(10),[5],[170],1418⟩,⟨270,(11),[5],[170],1418⟩,⟨270,(12),[5],[170],1419⟩,⟨270,(13),[5],[170],1419⟩,⟨270,(14),[5],[170],1419⟩,⟨270,(15),[5],[170],1419⟩,⟨273,(0),[5],[170],1098⟩,⟨273,(1),[5],[170],1099⟩,⟨273,(2),[5],[170],1100⟩,⟨273,(3),[5],[170],1100⟩,⟨273,(4),[5],[170],1100⟩,⟨273,(5),[5],[170],1098⟩,⟨273,(6),[5],[170],1099⟩,⟨273,(7),[5],[170],1101⟩,⟨273,(8),[5],[170],1102⟩,⟨273,(9),[5],[170],1101⟩,⟨275,(0),[5],[170],1420⟩,⟨275,(1),[5],[170],1420⟩,⟨275,(2),[5],[170],1421⟩,⟨275,(3),[5],[170],1422⟩,⟨275,(4),[5],[170],1423⟩,⟨275,(5),[5],[170],1424⟩,⟨275,(6),[5],[170],1424⟩,⟨275,(7),[5],[170],1424⟩,⟨275,(8),[5],[170],1422⟩,⟨275,(9),[5],[170],1423⟩,⟨278,(0),[5],[170],1108⟩,⟨278,(1),[5],[170],1109⟩,⟨278,(2),[5],[170],1110⟩,⟨278,(3),[5],[170],1110⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4352
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4353
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4354
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4355
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4356
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4357
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4358
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4359
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4360
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4361
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4362
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4363
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4364
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4365
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4366
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4367
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4368
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4369
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4370
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4371
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4372
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4373
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4374
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4375
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4376
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4377
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4378
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4379
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4380
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4381
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4382
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4383
end Section14Records_5_4352_4384

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4352_4384


namespace WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4384_4416
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_5_4384_4416
private theorem valid4384 : RecordDataValid section14Catalog 5 (⟨278,(4),[5],[170],1110⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1110,[3,5,7,8,9,11,12,15],1114⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4385 : RecordDataValid section14Catalog 5 (⟨278,(5),[5],[170],1108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1108,[3,5,7,8,9,11,12,15],1112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4386 : RecordDataValid section14Catalog 5 (⟨278,(6),[5],[170],1109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1109,[3,5,7,8,9,11,12,15],1113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4387 : RecordDataValid section14Catalog 5 (⟨278,(7),[5],[170],1111⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1111,[3,5,7,8,9,11,12,15],1115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4388 : RecordDataValid section14Catalog 5 (⟨278,(8),[5],[170],1112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1112,[3,5,7,8,9,11,12,15],1116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4389 : RecordDataValid section14Catalog 5 (⟨278,(9),[5],[170],1111⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1111,[3,5,7,8,9,11,12,15],1115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4390 : RecordDataValid section14Catalog 5 (⟨278,(10),[5],[170],1108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1108,[3,5,7,8,9,11,12,15],1112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4391 : RecordDataValid section14Catalog 5 (⟨278,(11),[5],[170],1109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1109,[3,5,7,8,9,11,12,15],1113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4392 : RecordDataValid section14Catalog 5 (⟨278,(12),[5],[170],1113⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1113,[3,5,7,8,9,11,12,15],1117⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4393 : RecordDataValid section14Catalog 5 (⟨278,(13),[5],[170],1112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1112,[3,5,7,8,9,11,12,15],1116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4394 : RecordDataValid section14Catalog 5 (⟨278,(14),[5],[170],1113⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1113,[3,5,7,8,9,11,12,15],1117⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4395 : RecordDataValid section14Catalog 5 (⟨278,(15),[5],[170],1108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1108,[3,5,7,8,9,11,12,15],1112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4396 : RecordDataValid section14Catalog 5 (⟨278,(16),[5],[170],1109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1109,[3,5,7,8,9,11,12,15],1113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4397 : RecordDataValid section14Catalog 5 (⟨278,(17),[5],[170],1111⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1111,[3,5,7,8,9,11,12,15],1115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4398 : RecordDataValid section14Catalog 5 (⟨278,(18),[5],[170],1112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1112,[3,5,7,8,9,11,12,15],1116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4399 : RecordDataValid section14Catalog 5 (⟨278,(19),[5],[170],1111⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1111,[3,5,7,8,9,11,12,15],1115⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4400 : RecordDataValid section14Catalog 5 (⟨278,(20),[5],[170],1108⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1108,[3,5,7,8,9,11,12,15],1112⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4401 : RecordDataValid section14Catalog 5 (⟨278,(21),[5],[170],1109⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1109,[3,5,7,8,9,11,12,15],1113⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4402 : RecordDataValid section14Catalog 5 (⟨278,(22),[5],[170],1114⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1114,[3,5,7,8,9,11,12,15],1118⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4403 : RecordDataValid section14Catalog 5 (⟨278,(23),[5],[170],1112⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1112,[3,5,7,8,9,11,12,15],1116⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4404 : RecordDataValid section14Catalog 5 (⟨278,(24),[5],[170],1114⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1114,[3,5,7,8,9,11,12,15],1118⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4405 : RecordDataValid section14Catalog 5 (⟨280,(0),[5],[170],1425⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1425,[5,8,9,12],1430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4406 : RecordDataValid section14Catalog 5 (⟨280,(1),[5],[170],1425⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1425,[5,8,9,12],1430⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4407 : RecordDataValid section14Catalog 5 (⟨280,(2),[5],[170],1426⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1426,[5,8,9,12],1431⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4408 : RecordDataValid section14Catalog 5 (⟨280,(3),[5],[170],1427⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1427,[5,8,9,12],1432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4409 : RecordDataValid section14Catalog 5 (⟨280,(4),[5],[170],1428⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1428,[5,8,9,12],1433⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4410 : RecordDataValid section14Catalog 5 (⟨280,(5),[5],[170],1429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1429,[5,8,9,12],1434⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4411 : RecordDataValid section14Catalog 5 (⟨280,(6),[5],[170],1429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1429,[5,8,9,12],1434⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4412 : RecordDataValid section14Catalog 5 (⟨280,(7),[5],[170],1429⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1429,[5,8,9,12],1434⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4413 : RecordDataValid section14Catalog 5 (⟨280,(8),[5],[170],1427⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1427,[5,8,9,12],1432⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4414 : RecordDataValid section14Catalog 5 (⟨280,(9),[5],[170],1428⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1428,[5,8,9,12],1433⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4415 : RecordDataValid section14Catalog 5 (⟨283,(0),[5],[170],1120⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1120,[3,5,7,8,9,11,12,15],1124⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0005_records_4384_4416 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4384).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4384).take 32 = [⟨278,(4),[5],[170],1110⟩,⟨278,(5),[5],[170],1108⟩,⟨278,(6),[5],[170],1109⟩,⟨278,(7),[5],[170],1111⟩,⟨278,(8),[5],[170],1112⟩,⟨278,(9),[5],[170],1111⟩,⟨278,(10),[5],[170],1108⟩,⟨278,(11),[5],[170],1109⟩,⟨278,(12),[5],[170],1113⟩,⟨278,(13),[5],[170],1112⟩,⟨278,(14),[5],[170],1113⟩,⟨278,(15),[5],[170],1108⟩,⟨278,(16),[5],[170],1109⟩,⟨278,(17),[5],[170],1111⟩,⟨278,(18),[5],[170],1112⟩,⟨278,(19),[5],[170],1111⟩,⟨278,(20),[5],[170],1108⟩,⟨278,(21),[5],[170],1109⟩,⟨278,(22),[5],[170],1114⟩,⟨278,(23),[5],[170],1112⟩,⟨278,(24),[5],[170],1114⟩,⟨280,(0),[5],[170],1425⟩,⟨280,(1),[5],[170],1425⟩,⟨280,(2),[5],[170],1426⟩,⟨280,(3),[5],[170],1427⟩,⟨280,(4),[5],[170],1428⟩,⟨280,(5),[5],[170],1429⟩,⟨280,(6),[5],[170],1429⟩,⟨280,(7),[5],[170],1429⟩,⟨280,(8),[5],[170],1427⟩,⟨280,(9),[5],[170],1428⟩,⟨283,(0),[5],[170],1120⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4384
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4385
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4386
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4387
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4388
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4389
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4390
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4391
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4392
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4393
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4394
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4395
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4396
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4397
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4398
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4399
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4400
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4401
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4402
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4403
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4404
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4405
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4406
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4407
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4408
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4409
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4410
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4411
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4412
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4413
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4414
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4415
end Section14Records_5_4384_4416

end WorkReverseInterface_Freiman_workReverse20260919_s0005_records_4384_4416

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4352).take 64, section14RecordValid section14Catalog 5 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (5 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 5 r
  exact (all_of_interval_split P xs 4352 4384 4416 (by decide) (by decide) (Freiman.workReverse20260919_s0005_records_4352_4384 hnum) (Freiman.workReverse20260919_s0005_records_4384_4416 hnum))

#print axioms solution
