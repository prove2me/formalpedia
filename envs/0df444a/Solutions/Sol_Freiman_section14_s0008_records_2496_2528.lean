-- Prove2me | solution 1 for Freiman.section14_s0008_records_2496_2528
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T08:05:46.271994+00:00
-- url     : https://prove2.me/submissions/ad091450-b29f-408e-a4e5-a6102863480c

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
namespace Section14Records_8_2496_2528
private theorem valid2496 : RecordDataValid section14Catalog 8 (⟨507,(2),[4,8,12],[6],1268⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1268,[4,8,12],1272⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2497 : RecordDataValid section14Catalog 8 (⟨507,(2),[4,8,12,16],[14],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2498 : RecordDataValid section14Catalog 8 (⟨507,(3),[4,8,12],[6],1267⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1267,[4,8,12],1271⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2499 : RecordDataValid section14Catalog 8 (⟨507,(3),[4,8,12,16],[14],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2500 : RecordDataValid section14Catalog 8 (⟨507,(4),[4,8,12],[6],1269⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1269,[4,8,12],1273⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2501 : RecordDataValid section14Catalog 8 (⟨507,(4),[4,8,12,16],[14],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2502 : RecordDataValid section14Catalog 8 (⟨507,(5),[4,8,12],[6],349⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨349,[1,2,3,4,5,6,7,8,9,10,11,12],350⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2503 : RecordDataValid section14Catalog 8 (⟨507,(5),[4,8,12,16],[14],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2504 : RecordDataValid section14Catalog 8 (⟨507,(6),[4,8,12],[6],1267⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1267,[4,8,12],1271⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2505 : RecordDataValid section14Catalog 8 (⟨507,(6),[4,8,12,16],[14],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2506 : RecordDataValid section14Catalog 8 (⟨507,(7),[4,8,12],[6],1268⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1268,[4,8,12],1272⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2507 : RecordDataValid section14Catalog 8 (⟨507,(7),[4,8,12,16],[14],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2508 : RecordDataValid section14Catalog 8 (⟨507,(8),[4,8,12],[6],1267⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1267,[4,8,12],1271⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2509 : RecordDataValid section14Catalog 8 (⟨507,(8),[4,8,12,16],[14],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2510 : RecordDataValid section14Catalog 8 (⟨507,(9),[4,8,12],[6],1269⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1269,[4,8,12],1273⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2511 : RecordDataValid section14Catalog 8 (⟨507,(9),[4,8,12,16],[14],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2512 : RecordDataValid section14Catalog 8 (⟨510,(0),[4,8,12],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2513 : RecordDataValid section14Catalog 8 (⟨510,(0),[4,8,12,16],[14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2514 : RecordDataValid section14Catalog 8 (⟨510,(1),[4,8,12],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2515 : RecordDataValid section14Catalog 8 (⟨510,(1),[4,8,12,16],[14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2516 : RecordDataValid section14Catalog 8 (⟨510,(2),[4,8,12],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2517 : RecordDataValid section14Catalog 8 (⟨510,(2),[4,8,12,16],[14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2518 : RecordDataValid section14Catalog 8 (⟨510,(3),[4,8,12],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2519 : RecordDataValid section14Catalog 8 (⟨510,(3),[4,8,12,16],[14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2520 : RecordDataValid section14Catalog 8 (⟨510,(4),[4,8,12],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2521 : RecordDataValid section14Catalog 8 (⟨510,(4),[4,8,12,16],[14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2522 : RecordDataValid section14Catalog 8 (⟨510,(5),[4,8,12],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2523 : RecordDataValid section14Catalog 8 (⟨510,(5),[4,8,12,16],[14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2524 : RecordDataValid section14Catalog 8 (⟨510,(6),[4,8,12],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2525 : RecordDataValid section14Catalog 8 (⟨510,(6),[4,8,12,16],[14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2526 : RecordDataValid section14Catalog 8 (⟨510,(7),[4,8,12],[6],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2527 : RecordDataValid section14Catalog 8 (⟨510,(7),[4,8,12,16],[14],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 2496).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 2496).take 32 = [⟨507,(2),[4,8,12],[6],1268⟩,⟨507,(2),[4,8,12,16],[14],3⟩,⟨507,(3),[4,8,12],[6],1267⟩,⟨507,(3),[4,8,12,16],[14],3⟩,⟨507,(4),[4,8,12],[6],1269⟩,⟨507,(4),[4,8,12,16],[14],3⟩,⟨507,(5),[4,8,12],[6],349⟩,⟨507,(5),[4,8,12,16],[14],3⟩,⟨507,(6),[4,8,12],[6],1267⟩,⟨507,(6),[4,8,12,16],[14],3⟩,⟨507,(7),[4,8,12],[6],1268⟩,⟨507,(7),[4,8,12,16],[14],3⟩,⟨507,(8),[4,8,12],[6],1267⟩,⟨507,(8),[4,8,12,16],[14],3⟩,⟨507,(9),[4,8,12],[6],1269⟩,⟨507,(9),[4,8,12,16],[14],3⟩,⟨510,(0),[4,8,12],[6],2⟩,⟨510,(0),[4,8,12,16],[14],2⟩,⟨510,(1),[4,8,12],[6],2⟩,⟨510,(1),[4,8,12,16],[14],2⟩,⟨510,(2),[4,8,12],[6],2⟩,⟨510,(2),[4,8,12,16],[14],2⟩,⟨510,(3),[4,8,12],[6],2⟩,⟨510,(3),[4,8,12,16],[14],2⟩,⟨510,(4),[4,8,12],[6],2⟩,⟨510,(4),[4,8,12,16],[14],2⟩,⟨510,(5),[4,8,12],[6],2⟩,⟨510,(5),[4,8,12,16],[14],2⟩,⟨510,(6),[4,8,12],[6],2⟩,⟨510,(6),[4,8,12,16],[14],2⟩,⟨510,(7),[4,8,12],[6],2⟩,⟨510,(7),[4,8,12,16],[14],2⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2496
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2497
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2498
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2499
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2500
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2501
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2502
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2503
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2504
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2505
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2506
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2507
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2508
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2509
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2510
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2511
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2512
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2513
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2514
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2515
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2516
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2517
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2518
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2519
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2520
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2521
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2522
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2523
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2524
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2525
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2526
  · exact recordValid_of_data section14Catalog 8 _ hnum valid2527
end Section14Records_8_2496_2528

#print axioms solution
