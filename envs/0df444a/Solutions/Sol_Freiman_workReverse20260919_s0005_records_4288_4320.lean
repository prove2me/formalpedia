-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_4288_4320
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:11:04.317435+00:00
-- url     : https://prove2.me/submissions/e3226728-573f-481c-b64e-9c00ba21482d

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
namespace Section14Records_5_4288_4320
private theorem valid4288 : RecordDataValid section14Catalog 5 (⟨262,(10),[5],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4289 : RecordDataValid section14Catalog 5 (⟨262,(11),[5],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4290 : RecordDataValid section14Catalog 5 (⟨262,(12),[5],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4291 : RecordDataValid section14Catalog 5 (⟨262,(13),[5],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4292 : RecordDataValid section14Catalog 5 (⟨262,(14),[5],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4293 : RecordDataValid section14Catalog 5 (⟨262,(15),[5],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4294 : RecordDataValid section14Catalog 5 (⟨262,(16),[5],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4295 : RecordDataValid section14Catalog 5 (⟨262,(17),[5],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4296 : RecordDataValid section14Catalog 5 (⟨262,(18),[5],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4297 : RecordDataValid section14Catalog 5 (⟨262,(19),[5],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4298 : RecordDataValid section14Catalog 5 (⟨262,(20),[5],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4299 : RecordDataValid section14Catalog 5 (⟨262,(21),[5],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4300 : RecordDataValid section14Catalog 5 (⟨262,(22),[5],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4301 : RecordDataValid section14Catalog 5 (⟨262,(23),[5],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4302 : RecordDataValid section14Catalog 5 (⟨262,(24),[5],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4303 : RecordDataValid section14Catalog 5 (⟨264,(0),[5],[170],1407⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1407,[5,8],1412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4304 : RecordDataValid section14Catalog 5 (⟨264,(1),[5],[170],1408⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1408,[5,8],1413⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4305 : RecordDataValid section14Catalog 5 (⟨264,(2),[5],[170],1407⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1407,[5,8],1412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4306 : RecordDataValid section14Catalog 5 (⟨264,(3),[5],[170],1409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1409,[5,8],1414⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4307 : RecordDataValid section14Catalog 5 (⟨264,(4),[5],[170],1410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1410,[5,8,9,12],1415⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4308 : RecordDataValid section14Catalog 5 (⟨264,(5),[5],[170],1407⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1407,[5,8],1412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4309 : RecordDataValid section14Catalog 5 (⟨264,(6),[5],[170],1408⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1408,[5,8],1413⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4310 : RecordDataValid section14Catalog 5 (⟨264,(7),[5],[170],1407⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1407,[5,8],1412⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4311 : RecordDataValid section14Catalog 5 (⟨264,(8),[5],[170],1409⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1409,[5,8],1414⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4312 : RecordDataValid section14Catalog 5 (⟨264,(9),[5],[170],1410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1410,[5,8,9,12],1415⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4313 : RecordDataValid section14Catalog 5 (⟨264,(10),[5],[170],1411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1411,[5,8],1416⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4314 : RecordDataValid section14Catalog 5 (⟨264,(11),[5],[170],1411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1411,[5,8],1416⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4315 : RecordDataValid section14Catalog 5 (⟨264,(12),[5],[170],1411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1411,[5,8],1416⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4316 : RecordDataValid section14Catalog 5 (⟨264,(13),[5],[170],1411⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1411,[5,8],1416⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4317 : RecordDataValid section14Catalog 5 (⟨264,(14),[5],[170],1410⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1410,[5,8,9,12],1415⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4318 : RecordDataValid section14Catalog 5 (⟨264,(15),[5],[170],1412⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1412,[5,8],1417⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid4319 : RecordDataValid section14Catalog 5 (⟨264,(16),[5],[170],1412⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1412,[5,8],1417⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4288).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 4288).take 32 = [⟨262,(10),[5],[170],3⟩,⟨262,(11),[5],[170],3⟩,⟨262,(12),[5],[170],3⟩,⟨262,(13),[5],[170],3⟩,⟨262,(14),[5],[170],3⟩,⟨262,(15),[5],[170],3⟩,⟨262,(16),[5],[170],3⟩,⟨262,(17),[5],[170],3⟩,⟨262,(18),[5],[170],3⟩,⟨262,(19),[5],[170],3⟩,⟨262,(20),[5],[170],3⟩,⟨262,(21),[5],[170],3⟩,⟨262,(22),[5],[170],3⟩,⟨262,(23),[5],[170],3⟩,⟨262,(24),[5],[170],3⟩,⟨264,(0),[5],[170],1407⟩,⟨264,(1),[5],[170],1408⟩,⟨264,(2),[5],[170],1407⟩,⟨264,(3),[5],[170],1409⟩,⟨264,(4),[5],[170],1410⟩,⟨264,(5),[5],[170],1407⟩,⟨264,(6),[5],[170],1408⟩,⟨264,(7),[5],[170],1407⟩,⟨264,(8),[5],[170],1409⟩,⟨264,(9),[5],[170],1410⟩,⟨264,(10),[5],[170],1411⟩,⟨264,(11),[5],[170],1411⟩,⟨264,(12),[5],[170],1411⟩,⟨264,(13),[5],[170],1411⟩,⟨264,(14),[5],[170],1410⟩,⟨264,(15),[5],[170],1412⟩,⟨264,(16),[5],[170],1412⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4288
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4289
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4290
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4291
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4292
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4293
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4294
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4295
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4296
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4297
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4298
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4299
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4300
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4301
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4302
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4303
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4304
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4305
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4306
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4307
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4308
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4309
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4310
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4311
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4312
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4313
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4314
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4315
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4316
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4317
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4318
  · exact recordValid_of_data section14Catalog 5 _ hnum valid4319
end Section14Records_5_4288_4320

#print axioms solution
