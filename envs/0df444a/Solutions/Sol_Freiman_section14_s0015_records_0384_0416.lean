-- Prove2me | solution 1 for Freiman.section14_s0015_records_0384_0416
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T17:51:01.237292+00:00
-- url     : https://prove2.me/submissions/5091cf6f-04e6-4c92-b4a7-12bfc94680b5

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
namespace Section14Records_15_384_416
private theorem valid384 : RecordDataValid section14Catalog 15 (⟨69,(24),[3,7,15],[11],380⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨380,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],381⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid385 : RecordDataValid section14Catalog 15 (⟨80,(5),[15],[11],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid386 : RecordDataValid section14Catalog 15 (⟨80,(7),[3,15],[11],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid387 : RecordDataValid section14Catalog 15 (⟨80,(8),[3,7,15],[11],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid388 : RecordDataValid section14Catalog 15 (⟨80,(9),[7,15],[11],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid389 : RecordDataValid section14Catalog 15 (⟨80,(15),[3,7,15],[11],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid390 : RecordDataValid section14Catalog 15 (⟨80,(16),[3,7,15],[11],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid391 : RecordDataValid section14Catalog 15 (⟨80,(17),[3,7,15],[11],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid392 : RecordDataValid section14Catalog 15 (⟨80,(19),[3,7,15],[11],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid393 : RecordDataValid section14Catalog 15 (⟨82,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],386⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨386,[1,2,3,5,6,7,9,10,11,13,14,15],387⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid394 : RecordDataValid section14Catalog 15 (⟨82,(-1),[1,3,5,7,9,11,13,15],[0],386⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨386,[1,2,3,5,6,7,9,10,11,13,14,15],387⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid395 : RecordDataValid section14Catalog 15 (⟨82,(-1),[3,4,7,8,12,15,16],[5],388⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨388,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],389⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid396 : RecordDataValid section14Catalog 15 (⟨82,(-1),[3,7,15],[2,3],386⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨386,[1,2,3,5,6,7,9,10,11,13,14,15],387⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid397 : RecordDataValid section14Catalog 15 (⟨82,(-1),[3,7,15],[4,6,7],388⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨388,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],389⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid398 : RecordDataValid section14Catalog 15 (⟨82,(-1),[3,7,15],[8],390⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨390,[1,2,3,5,6,7,13,14,15],391⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid399 : RecordDataValid section14Catalog 15 (⟨82,(-1),[3,7,15],[9],392⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨392,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],393⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid400 : RecordDataValid section14Catalog 15 (⟨82,(-1),[3,7,15],[11],628⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨628,[1,2,3,5,6,7,13,14,15],629⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid401 : RecordDataValid section14Catalog 15 (⟨82,(-1),[3,7,15],[12,13,14,15],630⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨630,[1,2,3,5,6,7,9,10,11,13,14,15],631⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid402 : RecordDataValid section14Catalog 15 (⟨82,(-1),[3,7,15],[10],919⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨919,[2,3,14,15],922⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid403 : RecordDataValid section14Catalog 15 (⟨153,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],631⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨631,[1,2,3,5,6,7,9,10,11,13,14,15],632⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid404 : RecordDataValid section14Catalog 15 (⟨153,(-1),[1,3,5,7,9,11,13,15],[0],631⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨631,[1,2,3,5,6,7,9,10,11,13,14,15],632⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid405 : RecordDataValid section14Catalog 15 (⟨153,(-1),[3,4,7,8,12,15,16],[5],633⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨633,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],634⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid406 : RecordDataValid section14Catalog 15 (⟨153,(-1),[3,7,15],[3],631⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨631,[1,2,3,5,6,7,9,10,11,13,14,15],632⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid407 : RecordDataValid section14Catalog 15 (⟨153,(-1),[3,7,15],[4,7],633⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨633,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],634⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid408 : RecordDataValid section14Catalog 15 (⟨153,(-1),[3,7,15],[8],635⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨635,[1,2,3,5,6,7,13,14,15],636⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid409 : RecordDataValid section14Catalog 15 (⟨153,(-1),[3,7,15],[9],637⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨637,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],638⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid410 : RecordDataValid section14Catalog 15 (⟨153,(-1),[3,7,15],[12,13,15],880⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨880,[1,2,3,5,6,7,9,10,11,13,14,15],882⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid411 : RecordDataValid section14Catalog 15 (⟨153,(-1),[3,15],[2],631⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨631,[1,2,3,5,6,7,9,10,11,13,14,15],632⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid412 : RecordDataValid section14Catalog 15 (⟨153,(-1),[3,15],[6],633⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨633,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],634⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid413 : RecordDataValid section14Catalog 15 (⟨153,(-1),[3,15],[14],880⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨880,[1,2,3,5,6,7,9,10,11,13,14,15],882⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid414 : RecordDataValid section14Catalog 15 (⟨153,(-1),[15],[11],878⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨878,[15],880⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid415 : RecordDataValid section14Catalog 15 (⟨157,(0),[3,4,7,8,15,16],[10],10⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 384).take 32, section14RecordValid section14Catalog 15 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (15 ∈ r.states))).drop 384).take 32 = [⟨69,(24),[3,7,15],[11],380⟩,⟨80,(5),[15],[11],3⟩,⟨80,(7),[3,15],[11],3⟩,⟨80,(8),[3,7,15],[11],3⟩,⟨80,(9),[7,15],[11],143⟩,⟨80,(15),[3,7,15],[11],3⟩,⟨80,(16),[3,7,15],[11],3⟩,⟨80,(17),[3,7,15],[11],48⟩,⟨80,(19),[3,7,15],[11],143⟩,⟨82,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],386⟩,⟨82,(-1),[1,3,5,7,9,11,13,15],[0],386⟩,⟨82,(-1),[3,4,7,8,12,15,16],[5],388⟩,⟨82,(-1),[3,7,15],[2,3],386⟩,⟨82,(-1),[3,7,15],[4,6,7],388⟩,⟨82,(-1),[3,7,15],[8],390⟩,⟨82,(-1),[3,7,15],[9],392⟩,⟨82,(-1),[3,7,15],[11],628⟩,⟨82,(-1),[3,7,15],[12,13,14,15],630⟩,⟨82,(-1),[3,7,15],[10],919⟩,⟨153,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],631⟩,⟨153,(-1),[1,3,5,7,9,11,13,15],[0],631⟩,⟨153,(-1),[3,4,7,8,12,15,16],[5],633⟩,⟨153,(-1),[3,7,15],[3],631⟩,⟨153,(-1),[3,7,15],[4,7],633⟩,⟨153,(-1),[3,7,15],[8],635⟩,⟨153,(-1),[3,7,15],[9],637⟩,⟨153,(-1),[3,7,15],[12,13,15],880⟩,⟨153,(-1),[3,15],[2],631⟩,⟨153,(-1),[3,15],[6],633⟩,⟨153,(-1),[3,15],[14],880⟩,⟨153,(-1),[15],[11],878⟩,⟨157,(0),[3,4,7,8,15,16],[10],10⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 15 _ hnum valid384
  · exact recordValid_of_data section14Catalog 15 _ hnum valid385
  · exact recordValid_of_data section14Catalog 15 _ hnum valid386
  · exact recordValid_of_data section14Catalog 15 _ hnum valid387
  · exact recordValid_of_data section14Catalog 15 _ hnum valid388
  · exact recordValid_of_data section14Catalog 15 _ hnum valid389
  · exact recordValid_of_data section14Catalog 15 _ hnum valid390
  · exact recordValid_of_data section14Catalog 15 _ hnum valid391
  · exact recordValid_of_data section14Catalog 15 _ hnum valid392
  · exact recordValid_of_data section14Catalog 15 _ hnum valid393
  · exact recordValid_of_data section14Catalog 15 _ hnum valid394
  · exact recordValid_of_data section14Catalog 15 _ hnum valid395
  · exact recordValid_of_data section14Catalog 15 _ hnum valid396
  · exact recordValid_of_data section14Catalog 15 _ hnum valid397
  · exact recordValid_of_data section14Catalog 15 _ hnum valid398
  · exact recordValid_of_data section14Catalog 15 _ hnum valid399
  · exact recordValid_of_data section14Catalog 15 _ hnum valid400
  · exact recordValid_of_data section14Catalog 15 _ hnum valid401
  · exact recordValid_of_data section14Catalog 15 _ hnum valid402
  · exact recordValid_of_data section14Catalog 15 _ hnum valid403
  · exact recordValid_of_data section14Catalog 15 _ hnum valid404
  · exact recordValid_of_data section14Catalog 15 _ hnum valid405
  · exact recordValid_of_data section14Catalog 15 _ hnum valid406
  · exact recordValid_of_data section14Catalog 15 _ hnum valid407
  · exact recordValid_of_data section14Catalog 15 _ hnum valid408
  · exact recordValid_of_data section14Catalog 15 _ hnum valid409
  · exact recordValid_of_data section14Catalog 15 _ hnum valid410
  · exact recordValid_of_data section14Catalog 15 _ hnum valid411
  · exact recordValid_of_data section14Catalog 15 _ hnum valid412
  · exact recordValid_of_data section14Catalog 15 _ hnum valid413
  · exact recordValid_of_data section14Catalog 15 _ hnum valid414
  · exact recordValid_of_data section14Catalog 15 _ hnum valid415
end Section14Records_15_384_416

#print axioms solution
