-- Prove2me | solution 1 for Freiman.section14_s0009_records_1536_1568
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T20:48:00.22328+00:00
-- url     : https://prove2.me/submissions/feb96028-26f2-4607-89bd-79323e79412f

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
namespace Section14Records_9_1536_1568
private theorem valid1536 : RecordDataValid section14Catalog 9 (⟨153,(-1),[1,5,9,13],[4],631⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨631,[1,2,3,5,6,7,9,10,11,13,14,15],632⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1537 : RecordDataValid section14Catalog 9 (⟨153,(-1),[2,6,9,10,14],[16,20],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1538 : RecordDataValid section14Catalog 9 (⟨153,(-1),[9],[8,12],631⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨631,[1,2,3,5,6,7,9,10,11,13,14,15],632⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1539 : RecordDataValid section14Catalog 9 (⟨153,(-1),[9],[51,55,59,63],880⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨880,[1,2,3,5,6,7,9,10,11,13,14,15],882⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1540 : RecordDataValid section14Catalog 9 (⟨153,(-1),[9,10],[32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1541 : RecordDataValid section14Catalog 9 (⟨153,(-1),[9,10],[9,13],631⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨631,[1,2,3,5,6,7,9,10,11,13,14,15],632⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1542 : RecordDataValid section14Catalog 9 (⟨153,(-1),[9,10],[24,28],632⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1543 : RecordDataValid section14Catalog 9 (⟨153,(-1),[9,10],[17,21,25,29],633⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨633,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],634⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1544 : RecordDataValid section14Catalog 9 (⟨153,(-1),[9,10],[34],634⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨634,[1,2,4,5,6,8,9,10,12,13,14,16],635⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1545 : RecordDataValid section14Catalog 9 (⟨153,(-1),[9,10],[35,39,43,47],636⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨636,[1,2,4,5,6,8,9,10,12,13,14,16],637⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1546 : RecordDataValid section14Catalog 9 (⟨153,(-1),[9,10],[38],637⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨637,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],638⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1547 : RecordDataValid section14Catalog 9 (⟨153,(-1),[9,10],[46],879⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨879,[1,2,4,5,6,8,9,10,12,13,14,16],881⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1548 : RecordDataValid section14Catalog 9 (⟨153,(-1),[9,10],[50,54,58,62],880⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨880,[1,2,3,5,6,7,9,10,11,13,14,15],882⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1549 : RecordDataValid section14Catalog 9 (⟨153,(-1),[9,10,13],[10,11,14,15,26,27,30,31],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1550 : RecordDataValid section14Catalog 9 (⟨155,(0),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1551 : RecordDataValid section14Catalog 9 (⟨155,(1),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1552 : RecordDataValid section14Catalog 9 (⟨155,(2),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1553 : RecordDataValid section14Catalog 9 (⟨155,(3),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1554 : RecordDataValid section14Catalog 9 (⟨155,(4),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1555 : RecordDataValid section14Catalog 9 (⟨155,(5),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1556 : RecordDataValid section14Catalog 9 (⟨155,(6),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1557 : RecordDataValid section14Catalog 9 (⟨155,(7),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1558 : RecordDataValid section14Catalog 9 (⟨155,(8),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1559 : RecordDataValid section14Catalog 9 (⟨155,(9),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1560 : RecordDataValid section14Catalog 9 (⟨155,(10),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1561 : RecordDataValid section14Catalog 9 (⟨155,(11),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1562 : RecordDataValid section14Catalog 9 (⟨155,(12),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1563 : RecordDataValid section14Catalog 9 (⟨155,(13),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1564 : RecordDataValid section14Catalog 9 (⟨155,(14),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1565 : RecordDataValid section14Catalog 9 (⟨155,(15),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1566 : RecordDataValid section14Catalog 9 (⟨155,(16),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid1567 : RecordDataValid section14Catalog 9 (⟨155,(17),[9,10],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 1536).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 1536).take 32 = [⟨153,(-1),[1,5,9,13],[4],631⟩,⟨153,(-1),[2,6,9,10,14],[16,20],632⟩,⟨153,(-1),[9],[8,12],631⟩,⟨153,(-1),[9],[51,55,59,63],880⟩,⟨153,(-1),[9,10],[32,33,36,37,40,41,44,45,48,49,52,53,56,57,60,61],2⟩,⟨153,(-1),[9,10],[9,13],631⟩,⟨153,(-1),[9,10],[24,28],632⟩,⟨153,(-1),[9,10],[17,21,25,29],633⟩,⟨153,(-1),[9,10],[34],634⟩,⟨153,(-1),[9,10],[35,39,43,47],636⟩,⟨153,(-1),[9,10],[38],637⟩,⟨153,(-1),[9,10],[46],879⟩,⟨153,(-1),[9,10],[50,54,58,62],880⟩,⟨153,(-1),[9,10,13],[10,11,14,15,26,27,30,31],2⟩,⟨155,(0),[9,10],[42],3⟩,⟨155,(1),[9,10],[42],3⟩,⟨155,(2),[9,10],[42],3⟩,⟨155,(3),[9,10],[42],3⟩,⟨155,(4),[9,10],[42],3⟩,⟨155,(5),[9,10],[42],3⟩,⟨155,(6),[9,10],[42],3⟩,⟨155,(7),[9,10],[42],3⟩,⟨155,(8),[9,10],[42],3⟩,⟨155,(9),[9,10],[42],3⟩,⟨155,(10),[9,10],[42],3⟩,⟨155,(11),[9,10],[42],3⟩,⟨155,(12),[9,10],[42],3⟩,⟨155,(13),[9,10],[42],3⟩,⟨155,(14),[9,10],[42],3⟩,⟨155,(15),[9,10],[42],3⟩,⟨155,(16),[9,10],[42],3⟩,⟨155,(17),[9,10],[42],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1536
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1537
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1538
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1539
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1540
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1541
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1542
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1543
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1544
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1545
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1546
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1547
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1548
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1549
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1550
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1551
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1552
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1553
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1554
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1555
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1556
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1557
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1558
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1559
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1560
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1561
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1562
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1563
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1564
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1565
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1566
  · exact recordValid_of_data section14Catalog 9 _ hnum valid1567
end Section14Records_9_1536_1568

#print axioms solution
