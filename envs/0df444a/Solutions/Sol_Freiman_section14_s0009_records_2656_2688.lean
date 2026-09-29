-- Prove2me | solution 1 for Freiman.section14_s0009_records_2656_2688
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T21:41:08.021579+00:00
-- url     : https://prove2.me/submissions/9e239401-b84c-475d-b28c-122344be6445

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
namespace Section14Records_9_2656_2688
private theorem valid2656 : RecordDataValid section14Catalog 9 (⟨295,(14),[9],[42],1447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1447,[5,8,9,12],1452⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2657 : RecordDataValid section14Catalog 9 (⟨295,(15),[9],[42],1449⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1449,[5,8,9,12],1454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2658 : RecordDataValid section14Catalog 9 (⟨295,(16),[9],[42],1449⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1449,[5,8,9,12],1454⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2659 : RecordDataValid section14Catalog 9 (⟨295,(17),[9],[42],1445⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1445,[5,8,9,12],1450⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2660 : RecordDataValid section14Catalog 9 (⟨295,(18),[9],[42],1446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1446,[5,8,9,12],1451⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2661 : RecordDataValid section14Catalog 9 (⟨295,(19),[9],[42],1447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1447,[5,8,9,12],1452⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2662 : RecordDataValid section14Catalog 9 (⟨295,(20),[9],[42],1450⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1450,[5,8,9,12],1455⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2663 : RecordDataValid section14Catalog 9 (⟨295,(21),[9],[42],1450⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1450,[5,8,9,12],1455⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2664 : RecordDataValid section14Catalog 9 (⟨295,(22),[9],[42],1450⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1450,[5,8,9,12],1455⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2665 : RecordDataValid section14Catalog 9 (⟨295,(23),[9],[42],1446⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1446,[5,8,9,12],1451⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2666 : RecordDataValid section14Catalog 9 (⟨295,(24),[9],[42],1447⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1447,[5,8,9,12],1452⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2667 : RecordDataValid section14Catalog 9 (⟨297,(0),[9],[42],1451⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1451,[5,8,9,12],1456⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2668 : RecordDataValid section14Catalog 9 (⟨297,(1),[9],[42],1452⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1452,[5,8,9,12],1457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2669 : RecordDataValid section14Catalog 9 (⟨297,(2),[9],[42],1453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1453,[5,8,9,12],1458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2670 : RecordDataValid section14Catalog 9 (⟨297,(3),[9],[42],1454⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1454,[5,8,9,12],1459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2671 : RecordDataValid section14Catalog 9 (⟨297,(4),[9],[42],1451⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1451,[5,8,9,12],1456⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2672 : RecordDataValid section14Catalog 9 (⟨297,(5),[9],[42],1452⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1452,[5,8,9,12],1457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2673 : RecordDataValid section14Catalog 9 (⟨297,(6),[9],[42],1455⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1455,[5,8,9,12],1460⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2674 : RecordDataValid section14Catalog 9 (⟨297,(7),[9],[42],1454⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1454,[5,8,9,12],1459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2675 : RecordDataValid section14Catalog 9 (⟨297,(8),[9],[42],1451⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1451,[5,8,9,12],1456⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2676 : RecordDataValid section14Catalog 9 (⟨297,(9),[9],[42],1452⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1452,[5,8,9,12],1457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2677 : RecordDataValid section14Catalog 9 (⟨297,(10),[9],[42],1453⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1453,[5,8,9,12],1458⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2678 : RecordDataValid section14Catalog 9 (⟨297,(11),[9],[42],1454⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1454,[5,8,9,12],1459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2679 : RecordDataValid section14Catalog 9 (⟨297,(12),[9],[42],1451⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1451,[5,8,9,12],1456⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2680 : RecordDataValid section14Catalog 9 (⟨297,(13),[9],[42],1452⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1452,[5,8,9,12],1457⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2681 : RecordDataValid section14Catalog 9 (⟨297,(14),[9],[42],1456⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1456,[5,8,9,12],1461⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2682 : RecordDataValid section14Catalog 9 (⟨297,(15),[9],[42],1454⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1454,[5,8,9,12],1459⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2683 : RecordDataValid section14Catalog 9 (⟨300,(0),[9],[42],1457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1457,[5,8,9,12],1462⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2684 : RecordDataValid section14Catalog 9 (⟨300,(1),[9],[42],1458⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1458,[5,8,9,12],1463⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2685 : RecordDataValid section14Catalog 9 (⟨300,(2),[9],[42],1457⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1457,[5,8,9,12],1462⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2686 : RecordDataValid section14Catalog 9 (⟨300,(3),[9],[42],1459⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1459,[5,8,9,12],1464⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2687 : RecordDataValid section14Catalog 9 (⟨300,(4),[9],[42],1460⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1460,[5,8,9,12],1465⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2656).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 2656).take 32 = [⟨295,(14),[9],[42],1447⟩,⟨295,(15),[9],[42],1449⟩,⟨295,(16),[9],[42],1449⟩,⟨295,(17),[9],[42],1445⟩,⟨295,(18),[9],[42],1446⟩,⟨295,(19),[9],[42],1447⟩,⟨295,(20),[9],[42],1450⟩,⟨295,(21),[9],[42],1450⟩,⟨295,(22),[9],[42],1450⟩,⟨295,(23),[9],[42],1446⟩,⟨295,(24),[9],[42],1447⟩,⟨297,(0),[9],[42],1451⟩,⟨297,(1),[9],[42],1452⟩,⟨297,(2),[9],[42],1453⟩,⟨297,(3),[9],[42],1454⟩,⟨297,(4),[9],[42],1451⟩,⟨297,(5),[9],[42],1452⟩,⟨297,(6),[9],[42],1455⟩,⟨297,(7),[9],[42],1454⟩,⟨297,(8),[9],[42],1451⟩,⟨297,(9),[9],[42],1452⟩,⟨297,(10),[9],[42],1453⟩,⟨297,(11),[9],[42],1454⟩,⟨297,(12),[9],[42],1451⟩,⟨297,(13),[9],[42],1452⟩,⟨297,(14),[9],[42],1456⟩,⟨297,(15),[9],[42],1454⟩,⟨300,(0),[9],[42],1457⟩,⟨300,(1),[9],[42],1458⟩,⟨300,(2),[9],[42],1457⟩,⟨300,(3),[9],[42],1459⟩,⟨300,(4),[9],[42],1460⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2656
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2657
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2658
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2659
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2660
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2661
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2662
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2663
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2664
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2665
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2666
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2667
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2668
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2669
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2670
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2671
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2672
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2673
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2674
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2675
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2676
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2677
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2678
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2679
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2680
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2681
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2682
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2683
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2684
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2685
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2686
  · exact recordValid_of_data section14Catalog 9 _ hnum valid2687
end Section14Records_9_2656_2688

#print axioms solution
