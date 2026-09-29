-- Prove2me | solution 1 for Freiman.section14_s0012_records_2528_2560
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T05:36:29.362908+00:00
-- url     : https://prove2.me/submissions/2f82ab82-b317-4cb6-b6c4-42b8cbb7e798

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
namespace Section14Records_12_2528_2560
private theorem valid2528 : RecordDataValid section14Catalog 12 (⟨567,(0),[12],[10],1670⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1670,[9,12],1675⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2529 : RecordDataValid section14Catalog 12 (⟨567,(1),[12],[10],1669⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1669,[9,12],1674⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2530 : RecordDataValid section14Catalog 12 (⟨567,(2),[12],[10],1670⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1670,[9,12],1675⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2531 : RecordDataValid section14Catalog 12 (⟨567,(3),[12],[10],1671⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1671,[9,12],1676⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2532 : RecordDataValid section14Catalog 12 (⟨567,(4),[12],[10],1275⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1275,[4,8,9,12,16],1279⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2533 : RecordDataValid section14Catalog 12 (⟨567,(5),[12],[10],1670⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1670,[9,12],1675⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2534 : RecordDataValid section14Catalog 12 (⟨567,(6),[12],[10],1669⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1669,[9,12],1674⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2535 : RecordDataValid section14Catalog 12 (⟨567,(7),[12],[10],1670⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1670,[9,12],1675⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2536 : RecordDataValid section14Catalog 12 (⟨567,(8),[12],[10],1671⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1671,[9,12],1676⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2537 : RecordDataValid section14Catalog 12 (⟨567,(9),[12],[10],1275⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1275,[4,8,9,12,16],1279⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2538 : RecordDataValid section14Catalog 12 (⟨572,(0),[12],[10],1649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1649,[9,10,11,12],1654⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2539 : RecordDataValid section14Catalog 12 (⟨572,(1),[12],[10],1650⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1650,[9,10,11,12],1655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2540 : RecordDataValid section14Catalog 12 (⟨572,(2),[12],[10],1673⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1673,[9,10,11,12],1678⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2541 : RecordDataValid section14Catalog 12 (⟨572,(3),[12],[10],1674⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1674,[9,10,11,12],1679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2542 : RecordDataValid section14Catalog 12 (⟨572,(4),[12],[10],890⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨890,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],892⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2543 : RecordDataValid section14Catalog 12 (⟨572,(5),[12],[10],1649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1649,[9,10,11,12],1654⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2544 : RecordDataValid section14Catalog 12 (⟨572,(6),[12],[10],1650⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1650,[9,10,11,12],1655⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2545 : RecordDataValid section14Catalog 12 (⟨572,(7),[12],[10],1673⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1673,[9,10,11,12],1678⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2546 : RecordDataValid section14Catalog 12 (⟨572,(8),[12],[10],1674⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1674,[9,10,11,12],1679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2547 : RecordDataValid section14Catalog 12 (⟨572,(9),[12],[10],890⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨890,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],892⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2548 : RecordDataValid section14Catalog 12 (⟨577,(0),[12],[10],904⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨904,[1,2,4,5,6,8,9,10,12],906⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2549 : RecordDataValid section14Catalog 12 (⟨577,(1),[12],[10],904⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨904,[1,2,4,5,6,8,9,10,12],906⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2550 : RecordDataValid section14Catalog 12 (⟨577,(2),[12],[10],900⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨900,[1,2,4,5,6,8,9,10,12],902⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2551 : RecordDataValid section14Catalog 12 (⟨577,(3),[12],[10],901⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨901,[1,2,4,5,6,8,9,10,12],903⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2552 : RecordDataValid section14Catalog 12 (⟨577,(4),[12],[10],902⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨902,[1,2,4,5,6,8,9,10,12],904⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2553 : RecordDataValid section14Catalog 12 (⟨577,(5),[12],[10],905⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨905,[1,2,4,5,6,8,9,10,12,13,14,16],907⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2554 : RecordDataValid section14Catalog 12 (⟨577,(6),[12],[10],905⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨905,[1,2,4,5,6,8,9,10,12,13,14,16],907⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2555 : RecordDataValid section14Catalog 12 (⟨577,(7),[12],[10],905⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨905,[1,2,4,5,6,8,9,10,12,13,14,16],907⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2556 : RecordDataValid section14Catalog 12 (⟨577,(8),[12],[10],901⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨901,[1,2,4,5,6,8,9,10,12],903⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2557 : RecordDataValid section14Catalog 12 (⟨577,(9),[12],[10],902⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨902,[1,2,4,5,6,8,9,10,12],904⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2558 : RecordDataValid section14Catalog 12 (⟨582,(0),[12],[10],1649⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1649,[9,10,11,12],1654⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2559 : RecordDataValid section14Catalog 12 (⟨582,(1),[12],[10],1676⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1676,[9,12],1681⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 2528).take 32, section14RecordValid section14Catalog 12 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (12 ∈ r.states))).drop 2528).take 32 = [⟨567,(0),[12],[10],1670⟩,⟨567,(1),[12],[10],1669⟩,⟨567,(2),[12],[10],1670⟩,⟨567,(3),[12],[10],1671⟩,⟨567,(4),[12],[10],1275⟩,⟨567,(5),[12],[10],1670⟩,⟨567,(6),[12],[10],1669⟩,⟨567,(7),[12],[10],1670⟩,⟨567,(8),[12],[10],1671⟩,⟨567,(9),[12],[10],1275⟩,⟨572,(0),[12],[10],1649⟩,⟨572,(1),[12],[10],1650⟩,⟨572,(2),[12],[10],1673⟩,⟨572,(3),[12],[10],1674⟩,⟨572,(4),[12],[10],890⟩,⟨572,(5),[12],[10],1649⟩,⟨572,(6),[12],[10],1650⟩,⟨572,(7),[12],[10],1673⟩,⟨572,(8),[12],[10],1674⟩,⟨572,(9),[12],[10],890⟩,⟨577,(0),[12],[10],904⟩,⟨577,(1),[12],[10],904⟩,⟨577,(2),[12],[10],900⟩,⟨577,(3),[12],[10],901⟩,⟨577,(4),[12],[10],902⟩,⟨577,(5),[12],[10],905⟩,⟨577,(6),[12],[10],905⟩,⟨577,(7),[12],[10],905⟩,⟨577,(8),[12],[10],901⟩,⟨577,(9),[12],[10],902⟩,⟨582,(0),[12],[10],1649⟩,⟨582,(1),[12],[10],1676⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2528
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2529
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2530
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2531
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2532
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2533
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2534
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2535
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2536
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2537
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2538
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2539
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2540
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2541
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2542
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2543
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2544
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2545
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2546
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2547
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2548
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2549
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2550
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2551
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2552
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2553
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2554
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2555
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2556
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2557
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2558
  · exact recordValid_of_data section14Catalog 12 _ hnum valid2559
end Section14Records_12_2528_2560

#print axioms solution
