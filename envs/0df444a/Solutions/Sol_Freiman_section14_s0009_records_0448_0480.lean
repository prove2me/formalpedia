-- Prove2me | solution 1 for Freiman.section14_s0009_records_0448_0480
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T20:06:13.262571+00:00
-- url     : https://prove2.me/submissions/c9720514-643c-4d57-ab2c-581a20a16694

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
namespace Section14Records_9_448_480
private theorem valid448 : RecordDataValid section14Catalog 9 (⟨38,(-1),[9],[47],251⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨251,[1,2,4,5,6,8,9,10,12,13,14,16],251⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid449 : RecordDataValid section14Catalog 9 (⟨38,(-1),[9],[51,55,62,63],340⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨340,[1,2,3,5,6,7,9,10,11,13,14,15],341⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid450 : RecordDataValid section14Catalog 9 (⟨38,(-1),[9,10],[32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid451 : RecordDataValid section14Catalog 9 (⟨38,(-1),[9,10],[9],61⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨61,[1,2,5,6,9,10,13,14],61⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid452 : RecordDataValid section14Catalog 9 (⟨38,(-1),[9,10],[24],69⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨69,[1,2,4,5,6,8,9,10,12,13,14,16],69⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid453 : RecordDataValid section14Catalog 9 (⟨38,(-1),[9,10],[25],70⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨70,[1,2,4,5,6,8,9,10,12,13,14,16],70⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid454 : RecordDataValid section14Catalog 9 (⟨38,(-1),[9,10],[43],207⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨207,[1,2,4,5,6,8,9,10,12,13,14,16],207⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid455 : RecordDataValid section14Catalog 9 (⟨38,(-1),[9,10],[58],244⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨244,[1,2,5,6,9,10,13,14],244⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid456 : RecordDataValid section14Catalog 9 (⟨38,(-1),[9,10],[17,21],248⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨248,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],248⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid457 : RecordDataValid section14Catalog 9 (⟨38,(-1),[9,10],[34],249⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨249,[1,2,4,5,6,8,9,10,12,13,14,16],249⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid458 : RecordDataValid section14Catalog 9 (⟨38,(-1),[9,10],[35,39],251⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨251,[1,2,4,5,6,8,9,10,12,13,14,16],251⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid459 : RecordDataValid section14Catalog 9 (⟨38,(-1),[9,10],[50,54],340⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨340,[1,2,3,5,6,7,9,10,11,13,14,15],341⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid460 : RecordDataValid section14Catalog 9 (⟨38,(-1),[9,10,13],[10,11,14,15,26,27,30,31],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid461 : RecordDataValid section14Catalog 9 (⟨40,(0),[9,10],[42,46],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid462 : RecordDataValid section14Catalog 9 (⟨40,(0),[9,10],[38],1532⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1532,[6,7,9,10,11],1537⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid463 : RecordDataValid section14Catalog 9 (⟨40,(1),[9,10],[42,46],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid464 : RecordDataValid section14Catalog 9 (⟨40,(1),[9,10],[38],1532⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1532,[6,7,9,10,11],1537⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid465 : RecordDataValid section14Catalog 9 (⟨40,(2),[9,10],[42,46],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid466 : RecordDataValid section14Catalog 9 (⟨40,(2),[9,10],[38],1532⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1532,[6,7,9,10,11],1537⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid467 : RecordDataValid section14Catalog 9 (⟨40,(3),[9,10],[42,46],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid468 : RecordDataValid section14Catalog 9 (⟨40,(3),[9,10],[38],1532⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1532,[6,7,9,10,11],1537⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid469 : RecordDataValid section14Catalog 9 (⟨40,(4),[9,10],[42,46],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid470 : RecordDataValid section14Catalog 9 (⟨40,(4),[9,10],[38],1532⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1532,[6,7,9,10,11],1537⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid471 : RecordDataValid section14Catalog 9 (⟨40,(5),[9,10],[42,46],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid472 : RecordDataValid section14Catalog 9 (⟨40,(5),[9,10],[38],1533⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1533,[6,7,9,10,11],1538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid473 : RecordDataValid section14Catalog 9 (⟨40,(6),[9,10],[42,46],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid474 : RecordDataValid section14Catalog 9 (⟨40,(6),[9,10],[38],1533⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1533,[6,7,9,10,11],1538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid475 : RecordDataValid section14Catalog 9 (⟨40,(7),[9,10],[42,46],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid476 : RecordDataValid section14Catalog 9 (⟨40,(7),[9,10],[38],1533⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1533,[6,7,9,10,11],1538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid477 : RecordDataValid section14Catalog 9 (⟨40,(8),[9,10],[42,46],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid478 : RecordDataValid section14Catalog 9 (⟨40,(8),[9,10],[38],1533⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1533,[6,7,9,10,11],1538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid479 : RecordDataValid section14Catalog 9 (⟨40,(9),[9,10],[42,46],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 448).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 448).take 32 = [⟨38,(-1),[9],[47],251⟩,⟨38,(-1),[9],[51,55,62,63],340⟩,⟨38,(-1),[9,10],[32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],2⟩,⟨38,(-1),[9,10],[9],61⟩,⟨38,(-1),[9,10],[24],69⟩,⟨38,(-1),[9,10],[25],70⟩,⟨38,(-1),[9,10],[43],207⟩,⟨38,(-1),[9,10],[58],244⟩,⟨38,(-1),[9,10],[17,21],248⟩,⟨38,(-1),[9,10],[34],249⟩,⟨38,(-1),[9,10],[35,39],251⟩,⟨38,(-1),[9,10],[50,54],340⟩,⟨38,(-1),[9,10,13],[10,11,14,15,26,27,30,31],2⟩,⟨40,(0),[9,10],[42,46],3⟩,⟨40,(0),[9,10],[38],1532⟩,⟨40,(1),[9,10],[42,46],3⟩,⟨40,(1),[9,10],[38],1532⟩,⟨40,(2),[9,10],[42,46],3⟩,⟨40,(2),[9,10],[38],1532⟩,⟨40,(3),[9,10],[42,46],3⟩,⟨40,(3),[9,10],[38],1532⟩,⟨40,(4),[9,10],[42,46],3⟩,⟨40,(4),[9,10],[38],1532⟩,⟨40,(5),[9,10],[42,46],3⟩,⟨40,(5),[9,10],[38],1533⟩,⟨40,(6),[9,10],[42,46],3⟩,⟨40,(6),[9,10],[38],1533⟩,⟨40,(7),[9,10],[42,46],3⟩,⟨40,(7),[9,10],[38],1533⟩,⟨40,(8),[9,10],[42,46],3⟩,⟨40,(8),[9,10],[38],1533⟩,⟨40,(9),[9,10],[42,46],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid448
  · exact recordValid_of_data section14Catalog 9 _ hnum valid449
  · exact recordValid_of_data section14Catalog 9 _ hnum valid450
  · exact recordValid_of_data section14Catalog 9 _ hnum valid451
  · exact recordValid_of_data section14Catalog 9 _ hnum valid452
  · exact recordValid_of_data section14Catalog 9 _ hnum valid453
  · exact recordValid_of_data section14Catalog 9 _ hnum valid454
  · exact recordValid_of_data section14Catalog 9 _ hnum valid455
  · exact recordValid_of_data section14Catalog 9 _ hnum valid456
  · exact recordValid_of_data section14Catalog 9 _ hnum valid457
  · exact recordValid_of_data section14Catalog 9 _ hnum valid458
  · exact recordValid_of_data section14Catalog 9 _ hnum valid459
  · exact recordValid_of_data section14Catalog 9 _ hnum valid460
  · exact recordValid_of_data section14Catalog 9 _ hnum valid461
  · exact recordValid_of_data section14Catalog 9 _ hnum valid462
  · exact recordValid_of_data section14Catalog 9 _ hnum valid463
  · exact recordValid_of_data section14Catalog 9 _ hnum valid464
  · exact recordValid_of_data section14Catalog 9 _ hnum valid465
  · exact recordValid_of_data section14Catalog 9 _ hnum valid466
  · exact recordValid_of_data section14Catalog 9 _ hnum valid467
  · exact recordValid_of_data section14Catalog 9 _ hnum valid468
  · exact recordValid_of_data section14Catalog 9 _ hnum valid469
  · exact recordValid_of_data section14Catalog 9 _ hnum valid470
  · exact recordValid_of_data section14Catalog 9 _ hnum valid471
  · exact recordValid_of_data section14Catalog 9 _ hnum valid472
  · exact recordValid_of_data section14Catalog 9 _ hnum valid473
  · exact recordValid_of_data section14Catalog 9 _ hnum valid474
  · exact recordValid_of_data section14Catalog 9 _ hnum valid475
  · exact recordValid_of_data section14Catalog 9 _ hnum valid476
  · exact recordValid_of_data section14Catalog 9 _ hnum valid477
  · exact recordValid_of_data section14Catalog 9 _ hnum valid478
  · exact recordValid_of_data section14Catalog 9 _ hnum valid479
end Section14Records_9_448_480

#print axioms solution
