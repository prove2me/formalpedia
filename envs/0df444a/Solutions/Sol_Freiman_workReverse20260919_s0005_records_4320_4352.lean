-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_4320_4352
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:12:17.306829+00:00
-- url     : https://prove2.me/submissions/240593dc-ce4c-45b2-9c86-90ef054beb37

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
namespace Section14Records_5_4320_4352
private theorem valid4320 : RecordDataValid section14Catalog 5 (⟨264,(17),[5],[170],1412⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1412,[5,8],1417⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4321 : RecordDataValid section14Catalog 5 (⟨264,(18),[5],[170],1412⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1412,[5,8],1417⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4322 : RecordDataValid section14Catalog 5 (⟨264,(19),[5],[170],1412⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1412,[5,8],1417⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4323 : RecordDataValid section14Catalog 5 (⟨264,(20),[5],[170],1413⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1413,[5,8],1418⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4324 : RecordDataValid section14Catalog 5 (⟨264,(21),[5],[170],1413⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1413,[5,8],1418⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4325 : RecordDataValid section14Catalog 5 (⟨264,(22),[5],[170],1413⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1413,[5,8],1418⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4326 : RecordDataValid section14Catalog 5 (⟨264,(23),[5],[170],1413⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1413,[5,8],1418⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4327 : RecordDataValid section14Catalog 5 (⟨264,(24),[5],[170],1413⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1413,[5,8],1418⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4328 : RecordDataValid section14Catalog 5 (⟨267,(0),[5],[170],1086⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1086,[3,5,7,8,9,11,12,15],1090⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4329 : RecordDataValid section14Catalog 5 (⟨267,(1),[5],[170],1087⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1087,[3,5,7,8,9,11,12,15],1091⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4330 : RecordDataValid section14Catalog 5 (⟨267,(2),[5],[170],1088⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1088,[3,5,7,8,9,11,12,15],1092⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4331 : RecordDataValid section14Catalog 5 (⟨267,(3),[5],[170],1089⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1089,[3,5,7,8,9,11,12,15],1093⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4332 : RecordDataValid section14Catalog 5 (⟨267,(4),[5],[170],1086⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1086,[3,5,7,8,9,11,12,15],1090⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4333 : RecordDataValid section14Catalog 5 (⟨267,(5),[5],[170],1087⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1087,[3,5,7,8,9,11,12,15],1091⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4334 : RecordDataValid section14Catalog 5 (⟨267,(6),[5],[170],1090⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1090,[3,5,7,8,9,11,12,15],1094⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4335 : RecordDataValid section14Catalog 5 (⟨267,(7),[5],[170],1089⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1089,[3,5,7,8,9,11,12,15],1093⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4336 : RecordDataValid section14Catalog 5 (⟨267,(8),[5],[170],1086⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1086,[3,5,7,8,9,11,12,15],1090⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4337 : RecordDataValid section14Catalog 5 (⟨267,(9),[5],[170],1087⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1087,[3,5,7,8,9,11,12,15],1091⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4338 : RecordDataValid section14Catalog 5 (⟨267,(10),[5],[170],1088⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1088,[3,5,7,8,9,11,12,15],1092⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4339 : RecordDataValid section14Catalog 5 (⟨267,(11),[5],[170],1089⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1089,[3,5,7,8,9,11,12,15],1093⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4340 : RecordDataValid section14Catalog 5 (⟨267,(12),[5],[170],1086⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1086,[3,5,7,8,9,11,12,15],1090⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4341 : RecordDataValid section14Catalog 5 (⟨267,(13),[5],[170],1087⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1087,[3,5,7,8,9,11,12,15],1091⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4342 : RecordDataValid section14Catalog 5 (⟨267,(14),[5],[170],1091⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1091,[3,5,7,8,9,11,12,15],1095⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4343 : RecordDataValid section14Catalog 5 (⟨267,(15),[5],[170],1089⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1089,[3,5,7,8,9,11,12,15],1093⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4344 : RecordDataValid section14Catalog 5 (⟨270,(0),[5],[170],1414⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1414,[5,8,9,12],1419⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4345 : RecordDataValid section14Catalog 5 (⟨270,(1),[5],[170],1415⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1415,[5,8,9,12],1420⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4346 : RecordDataValid section14Catalog 5 (⟨270,(2),[5],[170],1414⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1414,[5,8,9,12],1419⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4347 : RecordDataValid section14Catalog 5 (⟨270,(3),[5],[170],1416⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1416,[5,8,9,12],1421⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4348 : RecordDataValid section14Catalog 5 (⟨270,(4),[5],[170],1417⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1417,[5,8,9,12],1422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4349 : RecordDataValid section14Catalog 5 (⟨270,(5),[5],[170],1417⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1417,[5,8,9,12],1422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4350 : RecordDataValid section14Catalog 5 (⟨270,(6),[5],[170],1417⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1417,[5,8,9,12],1422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4351 : RecordDataValid section14Catalog 5 (⟨270,(7),[5],[170],1417⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1417,[5,8,9,12],1422⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4320).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4320).take 32 = [⟨264,(17),[5],[170],1412⟩,⟨264,(18),[5],[170],1412⟩,⟨264,(19),[5],[170],1412⟩,⟨264,(20),[5],[170],1413⟩,⟨264,(21),[5],[170],1413⟩,⟨264,(22),[5],[170],1413⟩,⟨264,(23),[5],[170],1413⟩,⟨264,(24),[5],[170],1413⟩,⟨267,(0),[5],[170],1086⟩,⟨267,(1),[5],[170],1087⟩,⟨267,(2),[5],[170],1088⟩,⟨267,(3),[5],[170],1089⟩,⟨267,(4),[5],[170],1086⟩,⟨267,(5),[5],[170],1087⟩,⟨267,(6),[5],[170],1090⟩,⟨267,(7),[5],[170],1089⟩,⟨267,(8),[5],[170],1086⟩,⟨267,(9),[5],[170],1087⟩,⟨267,(10),[5],[170],1088⟩,⟨267,(11),[5],[170],1089⟩,⟨267,(12),[5],[170],1086⟩,⟨267,(13),[5],[170],1087⟩,⟨267,(14),[5],[170],1091⟩,⟨267,(15),[5],[170],1089⟩,⟨270,(0),[5],[170],1414⟩,⟨270,(1),[5],[170],1415⟩,⟨270,(2),[5],[170],1414⟩,⟨270,(3),[5],[170],1416⟩,⟨270,(4),[5],[170],1417⟩,⟨270,(5),[5],[170],1417⟩,⟨270,(6),[5],[170],1417⟩,⟨270,(7),[5],[170],1417⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4320
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4321
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4322
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4323
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4324
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4325
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4326
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4327
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4328
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4329
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4330
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4331
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4332
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4333
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4334
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4335
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4336
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4337
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4338
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4339
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4340
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4341
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4342
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4343
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4344
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4345
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4346
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4347
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4348
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4349
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4350
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4351
end Section14Records_5_4320_4352

#print axioms solution
