-- Prove2me | solution 1 for Freiman.section14_s0009_records_2688_2720
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T21:44:46.000629+00:00
-- url     : https://prove2.me/submissions/41f7297a-01b5-4476-a67a-2f1ebaa45ded

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
namespace Section14Records_9_2688_2720
private theorem valid2688 : RecordDataValid section14Catalog 9 (⟨300,(5),[9],[42],1460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1460,[5,8,9,12],1465⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2689 : RecordDataValid section14Catalog 9 (⟨300,(6),[9],[42],1460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1460,[5,8,9,12],1465⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2690 : RecordDataValid section14Catalog 9 (⟨300,(7),[9],[42],1460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1460,[5,8,9,12],1465⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2691 : RecordDataValid section14Catalog 9 (⟨300,(8),[9],[42],1461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1461,[5,8,9,12],1466⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2692 : RecordDataValid section14Catalog 9 (⟨300,(9),[9],[42],1461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1461,[5,8,9,12],1466⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2693 : RecordDataValid section14Catalog 9 (⟨300,(10),[9],[42],1461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1461,[5,8,9,12],1466⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2694 : RecordDataValid section14Catalog 9 (⟨300,(11),[9],[42],1461⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1461,[5,8,9,12],1466⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2695 : RecordDataValid section14Catalog 9 (⟨300,(12),[9],[42],1462⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1462,[5,8,9,12],1467⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2696 : RecordDataValid section14Catalog 9 (⟨300,(13),[9],[42],1462⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1462,[5,8,9,12],1467⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2697 : RecordDataValid section14Catalog 9 (⟨300,(14),[9],[42],1462⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1462,[5,8,9,12],1467⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2698 : RecordDataValid section14Catalog 9 (⟨300,(15),[9],[42],1462⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1462,[5,8,9,12],1467⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2699 : RecordDataValid section14Catalog 9 (⟨302,(0),[9],[42],1463⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1463,[5,8,9,12],1468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2700 : RecordDataValid section14Catalog 9 (⟨302,(1),[9],[42],1464⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1464,[5,8,9,12],1469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2701 : RecordDataValid section14Catalog 9 (⟨302,(2),[9],[42],1465⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1465,[5,8,9,12],1470⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2702 : RecordDataValid section14Catalog 9 (⟨302,(3),[9],[42],1466⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1466,[5,8,9,12],1471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2703 : RecordDataValid section14Catalog 9 (⟨302,(4),[9],[42],1463⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1463,[5,8,9,12],1468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2704 : RecordDataValid section14Catalog 9 (⟨302,(5),[9],[42],1464⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1464,[5,8,9,12],1469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2705 : RecordDataValid section14Catalog 9 (⟨302,(6),[9],[42],1467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1467,[5,8,9,12],1472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2706 : RecordDataValid section14Catalog 9 (⟨302,(7),[9],[42],1466⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1466,[5,8,9,12],1471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2707 : RecordDataValid section14Catalog 9 (⟨302,(8),[9],[42],1463⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1463,[5,8,9,12],1468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2708 : RecordDataValid section14Catalog 9 (⟨302,(9),[9],[42],1464⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1464,[5,8,9,12],1469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2709 : RecordDataValid section14Catalog 9 (⟨302,(10),[9],[42],1465⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1465,[5,8,9,12],1470⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2710 : RecordDataValid section14Catalog 9 (⟨302,(11),[9],[42],1466⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1466,[5,8,9,12],1471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2711 : RecordDataValid section14Catalog 9 (⟨302,(12),[9],[42],1463⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1463,[5,8,9,12],1468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2712 : RecordDataValid section14Catalog 9 (⟨302,(13),[9],[42],1464⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1464,[5,8,9,12],1469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2713 : RecordDataValid section14Catalog 9 (⟨302,(14),[9],[42],1468⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1468,[5,8,9,12],1473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2714 : RecordDataValid section14Catalog 9 (⟨302,(15),[9],[42],1466⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1466,[5,8,9,12],1471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2715 : RecordDataValid section14Catalog 9 (⟨305,(0),[9],[42],1469⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1469,[5,8,9,12],1474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2716 : RecordDataValid section14Catalog 9 (⟨305,(1),[9],[42],1470⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1470,[5,8,9,12],1475⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2717 : RecordDataValid section14Catalog 9 (⟨305,(2),[9],[42],1471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1471,[5,8,9,12],1476⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2718 : RecordDataValid section14Catalog 9 (⟨305,(3),[9],[42],1472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1472,[5,8,9,12],1477⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2719 : RecordDataValid section14Catalog 9 (⟨307,(0),[9],[42],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2688).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2688).take 32 = [⟨300,(5),[9],[42],1460⟩,⟨300,(6),[9],[42],1460⟩,⟨300,(7),[9],[42],1460⟩,⟨300,(8),[9],[42],1461⟩,⟨300,(9),[9],[42],1461⟩,⟨300,(10),[9],[42],1461⟩,⟨300,(11),[9],[42],1461⟩,⟨300,(12),[9],[42],1462⟩,⟨300,(13),[9],[42],1462⟩,⟨300,(14),[9],[42],1462⟩,⟨300,(15),[9],[42],1462⟩,⟨302,(0),[9],[42],1463⟩,⟨302,(1),[9],[42],1464⟩,⟨302,(2),[9],[42],1465⟩,⟨302,(3),[9],[42],1466⟩,⟨302,(4),[9],[42],1463⟩,⟨302,(5),[9],[42],1464⟩,⟨302,(6),[9],[42],1467⟩,⟨302,(7),[9],[42],1466⟩,⟨302,(8),[9],[42],1463⟩,⟨302,(9),[9],[42],1464⟩,⟨302,(10),[9],[42],1465⟩,⟨302,(11),[9],[42],1466⟩,⟨302,(12),[9],[42],1463⟩,⟨302,(13),[9],[42],1464⟩,⟨302,(14),[9],[42],1468⟩,⟨302,(15),[9],[42],1466⟩,⟨305,(0),[9],[42],1469⟩,⟨305,(1),[9],[42],1470⟩,⟨305,(2),[9],[42],1471⟩,⟨305,(3),[9],[42],1472⟩,⟨307,(0),[9],[42],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2688
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2689
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2690
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2691
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2692
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2693
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2694
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2695
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2696
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2697
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2698
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2699
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2700
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2701
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2702
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2703
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2704
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2705
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2706
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2707
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2708
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2709
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2710
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2711
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2712
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2713
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2714
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2715
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2716
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2717
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2718
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2719
end Section14Records_9_2688_2720

#print axioms solution
