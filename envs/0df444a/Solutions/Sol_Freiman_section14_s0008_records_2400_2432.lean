-- Prove2me | solution 1 for Freiman.section14_s0008_records_2400_2432
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T08:02:34.831981+00:00
-- url     : https://prove2.me/submissions/705a495b-3e44-42ad-a49d-981af5c86dcc

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
namespace Section14Records_8_2400_2432
private theorem valid2400 : RecordDataValid section14Catalog 8 (⟨321,(8),[8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2401 : RecordDataValid section14Catalog 8 (⟨321,(9),[8,12],[10],1510⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1510,[5,8,9,12],1515⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2402 : RecordDataValid section14Catalog 8 (⟨321,(10),[8,12],[10],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2403 : RecordDataValid section14Catalog 8 (⟨321,(11),[8,12],[10],1497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1497,[5,8,9,12],1502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2404 : RecordDataValid section14Catalog 8 (⟨321,(12),[8,12],[10],1511⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1511,[5,8,9,12],1516⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2405 : RecordDataValid section14Catalog 8 (⟨321,(13),[8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2406 : RecordDataValid section14Catalog 8 (⟨321,(14),[8,12],[10],1511⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1511,[5,8,9,12],1516⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2407 : RecordDataValid section14Catalog 8 (⟨321,(15),[8,12],[10],625⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨625,[1,2,4,5,6,8,9,10,12],626⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2408 : RecordDataValid section14Catalog 8 (⟨321,(16),[8,12],[10],626⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨626,[1,2,4,5,6,8,9,10,12],627⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2409 : RecordDataValid section14Catalog 8 (⟨321,(17),[8,12],[10],286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨286,[1,2,4,5,6,8,9,10,12],287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2410 : RecordDataValid section14Catalog 8 (⟨321,(18),[8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2411 : RecordDataValid section14Catalog 8 (⟨321,(19),[8,12],[10],286⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨286,[1,2,4,5,6,8,9,10,12],287⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2412 : RecordDataValid section14Catalog 8 (⟨321,(20),[8,12],[10],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2413 : RecordDataValid section14Catalog 8 (⟨321,(21),[8,12],[10],1497⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1497,[5,8,9,12],1502⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2414 : RecordDataValid section14Catalog 8 (⟨321,(22),[8,12],[10],1512⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1512,[5,8,9,12],1517⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2415 : RecordDataValid section14Catalog 8 (⟨321,(23),[8,12],[10],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2416 : RecordDataValid section14Catalog 8 (⟨321,(24),[8,12],[10],1512⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1512,[5,8,9,12],1517⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2417 : RecordDataValid section14Catalog 8 (⟨478,(0),[4,8,12,16],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2418 : RecordDataValid section14Catalog 8 (⟨478,(1),[4,8,12,16],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2419 : RecordDataValid section14Catalog 8 (⟨478,(2),[4,8,12,16],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2420 : RecordDataValid section14Catalog 8 (⟨478,(3),[4,8,12,16],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2421 : RecordDataValid section14Catalog 8 (⟨478,(4),[4,8,12,16],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2422 : RecordDataValid section14Catalog 8 (⟨478,(5),[4,8,12,16],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2423 : RecordDataValid section14Catalog 8 (⟨478,(6),[4,8,12,16],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2424 : RecordDataValid section14Catalog 8 (⟨478,(7),[4,8,12,16],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2425 : RecordDataValid section14Catalog 8 (⟨478,(8),[4,8,12,16],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2426 : RecordDataValid section14Catalog 8 (⟨478,(9),[4,8,12,16],[10],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2427 : RecordDataValid section14Catalog 8 (⟨483,(0),[4,8,12,16],[6],1250⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1250,[4,8,12,16],1254⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2428 : RecordDataValid section14Catalog 8 (⟨483,(1),[4,8,12,16],[6],1251⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1251,[4,8,12,16],1255⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2429 : RecordDataValid section14Catalog 8 (⟨483,(2),[4,8,12,16],[6],1252⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1252,[4,8,12,16],1256⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2430 : RecordDataValid section14Catalog 8 (⟨483,(3),[4,8,12,16],[6],1251⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1251,[4,8,12,16],1255⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2431 : RecordDataValid section14Catalog 8 (⟨483,(4),[4,8,12,16],[6],1253⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1253,[4,8,12,16],1257⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 2400).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 2400).take 32 = [⟨321,(8),[8,12],[10],101⟩,⟨321,(9),[8,12],[10],1510⟩,⟨321,(10),[8,12],[10],882⟩,⟨321,(11),[8,12],[10],1497⟩,⟨321,(12),[8,12],[10],1511⟩,⟨321,(13),[8,12],[10],101⟩,⟨321,(14),[8,12],[10],1511⟩,⟨321,(15),[8,12],[10],625⟩,⟨321,(16),[8,12],[10],626⟩,⟨321,(17),[8,12],[10],286⟩,⟨321,(18),[8,12],[10],101⟩,⟨321,(19),[8,12],[10],286⟩,⟨321,(20),[8,12],[10],882⟩,⟨321,(21),[8,12],[10],1497⟩,⟨321,(22),[8,12],[10],1512⟩,⟨321,(23),[8,12],[10],101⟩,⟨321,(24),[8,12],[10],1512⟩,⟨478,(0),[4,8,12,16],[10],3⟩,⟨478,(1),[4,8,12,16],[10],3⟩,⟨478,(2),[4,8,12,16],[10],3⟩,⟨478,(3),[4,8,12,16],[10],3⟩,⟨478,(4),[4,8,12,16],[10],3⟩,⟨478,(5),[4,8,12,16],[10],3⟩,⟨478,(6),[4,8,12,16],[10],3⟩,⟨478,(7),[4,8,12,16],[10],3⟩,⟨478,(8),[4,8,12,16],[10],3⟩,⟨478,(9),[4,8,12,16],[10],3⟩,⟨483,(0),[4,8,12,16],[6],1250⟩,⟨483,(1),[4,8,12,16],[6],1251⟩,⟨483,(2),[4,8,12,16],[6],1252⟩,⟨483,(3),[4,8,12,16],[6],1251⟩,⟨483,(4),[4,8,12,16],[6],1253⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2400
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2401
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2402
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2403
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2404
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2405
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2406
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2407
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2408
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2409
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2410
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2411
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2412
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2413
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2414
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2415
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2416
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2417
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2418
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2419
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2420
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2421
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2422
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2423
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2424
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2425
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2426
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2427
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2428
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2429
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2430
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2431
end Section14Records_8_2400_2432

#print axioms solution
