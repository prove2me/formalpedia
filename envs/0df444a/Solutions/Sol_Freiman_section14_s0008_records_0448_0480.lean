-- Prove2me | solution 1 for Freiman.section14_s0008_records_0448_0480
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T06:57:34.759342+00:00
-- url     : https://prove2.me/submissions/09479a47-f8d4-46af-910c-319266007710

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
namespace Section14Records_8_448_480
private theorem valid448 : RecordDataValid section14Catalog 8 (⟨69,(21),[4,8,12,16],[14],271⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨271,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],272⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid449 : RecordDataValid section14Catalog 8 (⟨69,(21),[8,12],[6],271⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨271,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],272⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid450 : RecordDataValid section14Catalog 8 (⟨69,(22),[4,8,12],[6],199⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨199,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],199⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid451 : RecordDataValid section14Catalog 8 (⟨69,(22),[4,8,12,16],[14],380⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨380,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],381⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid452 : RecordDataValid section14Catalog 8 (⟨69,(23),[4,8,12],[6],199⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨199,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],199⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid453 : RecordDataValid section14Catalog 8 (⟨69,(23),[4,8,12,16],[14],380⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨380,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],381⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid454 : RecordDataValid section14Catalog 8 (⟨69,(24),[4,8,12],[6],199⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨199,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],199⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid455 : RecordDataValid section14Catalog 8 (⟨69,(24),[4,8,12,16],[14],380⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨380,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],381⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid456 : RecordDataValid section14Catalog 8 (⟨72,(0),[4,8,12],[6],354⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨354,[1,2,4,5,6,8,9,10,12],355⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid457 : RecordDataValid section14Catalog 8 (⟨72,(0),[8,12],[14],1399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1399,[5,6,8,9,10,12],1404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid458 : RecordDataValid section14Catalog 8 (⟨72,(1),[4,8,12],[6],355⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨355,[1,2,4,5,6,8,9,10,12],356⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid459 : RecordDataValid section14Catalog 8 (⟨72,(1),[8,12],[14],1400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1400,[5,6,8,9,10,12],1405⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid460 : RecordDataValid section14Catalog 8 (⟨72,(2),[4,8,12],[6],356⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨356,[1,2,4,5,6,8,9,10,12],357⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid461 : RecordDataValid section14Catalog 8 (⟨72,(2),[8,12],[14],1401⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1401,[5,6,8,9,10,12],1406⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid462 : RecordDataValid section14Catalog 8 (⟨72,(3),[4,8,12],[6],357⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨357,[1,2,4,5,6,8,9,10,12],358⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid463 : RecordDataValid section14Catalog 8 (⟨72,(3),[8,12],[14],1402⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1402,[5,6,8,9,10,12],1407⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid464 : RecordDataValid section14Catalog 8 (⟨72,(4),[4,8,12],[6],354⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨354,[1,2,4,5,6,8,9,10,12],355⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid465 : RecordDataValid section14Catalog 8 (⟨72,(4),[8,12],[14],1399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1399,[5,6,8,9,10,12],1404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid466 : RecordDataValid section14Catalog 8 (⟨72,(5),[4,8,12],[6],355⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨355,[1,2,4,5,6,8,9,10,12],356⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid467 : RecordDataValid section14Catalog 8 (⟨72,(5),[8,12],[14],1400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1400,[5,6,8,9,10,12],1405⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid468 : RecordDataValid section14Catalog 8 (⟨72,(6),[4,8,12],[6],358⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨358,[1,2,4,5,6,8,9,10,12],359⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid469 : RecordDataValid section14Catalog 8 (⟨72,(6),[8,12],[14],1403⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1403,[5,6,8,9,10,12],1408⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid470 : RecordDataValid section14Catalog 8 (⟨72,(7),[4,8,12],[6],357⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨357,[1,2,4,5,6,8,9,10,12],358⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid471 : RecordDataValid section14Catalog 8 (⟨72,(7),[8,12],[14],1402⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1402,[5,6,8,9,10,12],1407⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid472 : RecordDataValid section14Catalog 8 (⟨72,(8),[4,8,12],[6],354⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨354,[1,2,4,5,6,8,9,10,12],355⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid473 : RecordDataValid section14Catalog 8 (⟨72,(8),[8,12],[14],1399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1399,[5,6,8,9,10,12],1404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid474 : RecordDataValid section14Catalog 8 (⟨72,(9),[4,8,12],[6],355⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨355,[1,2,4,5,6,8,9,10,12],356⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid475 : RecordDataValid section14Catalog 8 (⟨72,(9),[8,12],[14],1400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1400,[5,6,8,9,10,12],1405⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid476 : RecordDataValid section14Catalog 8 (⟨72,(10),[4,8,12],[6],356⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨356,[1,2,4,5,6,8,9,10,12],357⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid477 : RecordDataValid section14Catalog 8 (⟨72,(10),[8,12],[14],1401⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1401,[5,6,8,9,10,12],1406⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid478 : RecordDataValid section14Catalog 8 (⟨72,(11),[4,8,12],[6],357⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨357,[1,2,4,5,6,8,9,10,12],358⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid479 : RecordDataValid section14Catalog 8 (⟨72,(11),[8,12],[14],1402⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1402,[5,6,8,9,10,12],1407⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 448).take 32, section14RecordValid section14Catalog 8 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (8 ∈ r.states))).drop 448).take 32 = [⟨69,(21),[4,8,12,16],[14],271⟩,⟨69,(21),[8,12],[6],271⟩,⟨69,(22),[4,8,12],[6],199⟩,⟨69,(22),[4,8,12,16],[14],380⟩,⟨69,(23),[4,8,12],[6],199⟩,⟨69,(23),[4,8,12,16],[14],380⟩,⟨69,(24),[4,8,12],[6],199⟩,⟨69,(24),[4,8,12,16],[14],380⟩,⟨72,(0),[4,8,12],[6],354⟩,⟨72,(0),[8,12],[14],1399⟩,⟨72,(1),[4,8,12],[6],355⟩,⟨72,(1),[8,12],[14],1400⟩,⟨72,(2),[4,8,12],[6],356⟩,⟨72,(2),[8,12],[14],1401⟩,⟨72,(3),[4,8,12],[6],357⟩,⟨72,(3),[8,12],[14],1402⟩,⟨72,(4),[4,8,12],[6],354⟩,⟨72,(4),[8,12],[14],1399⟩,⟨72,(5),[4,8,12],[6],355⟩,⟨72,(5),[8,12],[14],1400⟩,⟨72,(6),[4,8,12],[6],358⟩,⟨72,(6),[8,12],[14],1403⟩,⟨72,(7),[4,8,12],[6],357⟩,⟨72,(7),[8,12],[14],1402⟩,⟨72,(8),[4,8,12],[6],354⟩,⟨72,(8),[8,12],[14],1399⟩,⟨72,(9),[4,8,12],[6],355⟩,⟨72,(9),[8,12],[14],1400⟩,⟨72,(10),[4,8,12],[6],356⟩,⟨72,(10),[8,12],[14],1401⟩,⟨72,(11),[4,8,12],[6],357⟩,⟨72,(11),[8,12],[14],1402⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 8 _ hnum valid448
  · exact recordValid_of_data section14Catalog 8 _ hnum valid449
  · exact recordValid_of_data section14Catalog 8 _ hnum valid450
  · exact recordValid_of_data section14Catalog 8 _ hnum valid451
  · exact recordValid_of_data section14Catalog 8 _ hnum valid452
  · exact recordValid_of_data section14Catalog 8 _ hnum valid453
  · exact recordValid_of_data section14Catalog 8 _ hnum valid454
  · exact recordValid_of_data section14Catalog 8 _ hnum valid455
  · exact recordValid_of_data section14Catalog 8 _ hnum valid456
  · exact recordValid_of_data section14Catalog 8 _ hnum valid457
  · exact recordValid_of_data section14Catalog 8 _ hnum valid458
  · exact recordValid_of_data section14Catalog 8 _ hnum valid459
  · exact recordValid_of_data section14Catalog 8 _ hnum valid460
  · exact recordValid_of_data section14Catalog 8 _ hnum valid461
  · exact recordValid_of_data section14Catalog 8 _ hnum valid462
  · exact recordValid_of_data section14Catalog 8 _ hnum valid463
  · exact recordValid_of_data section14Catalog 8 _ hnum valid464
  · exact recordValid_of_data section14Catalog 8 _ hnum valid465
  · exact recordValid_of_data section14Catalog 8 _ hnum valid466
  · exact recordValid_of_data section14Catalog 8 _ hnum valid467
  · exact recordValid_of_data section14Catalog 8 _ hnum valid468
  · exact recordValid_of_data section14Catalog 8 _ hnum valid469
  · exact recordValid_of_data section14Catalog 8 _ hnum valid470
  · exact recordValid_of_data section14Catalog 8 _ hnum valid471
  · exact recordValid_of_data section14Catalog 8 _ hnum valid472
  · exact recordValid_of_data section14Catalog 8 _ hnum valid473
  · exact recordValid_of_data section14Catalog 8 _ hnum valid474
  · exact recordValid_of_data section14Catalog 8 _ hnum valid475
  · exact recordValid_of_data section14Catalog 8 _ hnum valid476
  · exact recordValid_of_data section14Catalog 8 _ hnum valid477
  · exact recordValid_of_data section14Catalog 8 _ hnum valid478
  · exact recordValid_of_data section14Catalog 8 _ hnum valid479
end Section14Records_8_448_480

#print axioms solution
