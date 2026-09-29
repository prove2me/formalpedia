-- Prove2me | solution 1 for Freiman.section14_s0010_records_0608_0640
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T16:44:31.423805+00:00
-- url     : https://prove2.me/submissions/7935500f-c2e4-4bf2-ac96-765a5993801b

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
namespace Section14Records_10_608_640
private theorem valid608 : RecordDataValid section14Catalog 10 (⟨50,(9),[9,10],[42],302⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨302,[1,2,4,5,6,8,9,10,12],303⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid609 : RecordDataValid section14Catalog 10 (⟨50,(9),[9,10],[38],332⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨332,[1,2,4,5,6,8,9,10,12],333⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid610 : RecordDataValid section14Catalog 10 (⟨50,(9),[10],[46],1400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1400,[5,6,8,9,10,12],1405⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid611 : RecordDataValid section14Catalog 10 (⟨50,(10),[9,10],[42],303⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨303,[1,2,4,5,6,8,9,10,12],304⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid612 : RecordDataValid section14Catalog 10 (⟨50,(10),[9,10],[38],333⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨333,[1,2,4,5,6,8,9,10,12],334⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid613 : RecordDataValid section14Catalog 10 (⟨50,(10),[10],[46],1401⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1401,[5,6,8,9,10,12],1406⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid614 : RecordDataValid section14Catalog 10 (⟨50,(11),[9,10],[42],304⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨304,[1,2,4,5,6,8,9,10,12],305⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid615 : RecordDataValid section14Catalog 10 (⟨50,(11),[9,10],[38],334⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨334,[1,2,4,5,6,8,9,10,12],335⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid616 : RecordDataValid section14Catalog 10 (⟨50,(11),[10],[46],1402⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1402,[5,6,8,9,10,12],1407⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid617 : RecordDataValid section14Catalog 10 (⟨50,(12),[9,10],[42],301⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨301,[1,2,4,5,6,8,9,10,12],302⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid618 : RecordDataValid section14Catalog 10 (⟨50,(12),[9,10],[38],331⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨331,[1,2,4,5,6,8,9,10,12],332⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid619 : RecordDataValid section14Catalog 10 (⟨50,(12),[10],[46],1399⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1399,[5,6,8,9,10,12],1404⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid620 : RecordDataValid section14Catalog 10 (⟨50,(13),[9,10],[42],302⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨302,[1,2,4,5,6,8,9,10,12],303⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid621 : RecordDataValid section14Catalog 10 (⟨50,(13),[9,10],[38],332⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨332,[1,2,4,5,6,8,9,10,12],333⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid622 : RecordDataValid section14Catalog 10 (⟨50,(13),[10],[46],1400⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1400,[5,6,8,9,10,12],1405⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid623 : RecordDataValid section14Catalog 10 (⟨50,(14),[9,10],[42],306⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨306,[1,2,4,5,6,8,9,10,12],307⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid624 : RecordDataValid section14Catalog 10 (⟨50,(14),[9,10],[38],336⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨336,[1,2,4,5,6,8,9,10,12],337⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid625 : RecordDataValid section14Catalog 10 (⟨50,(14),[10],[46],1404⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1404,[5,6,8,9,10,12],1409⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid626 : RecordDataValid section14Catalog 10 (⟨50,(15),[9,10],[42],304⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨304,[1,2,4,5,6,8,9,10,12],305⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid627 : RecordDataValid section14Catalog 10 (⟨50,(15),[9,10],[38],334⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨334,[1,2,4,5,6,8,9,10,12],335⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid628 : RecordDataValid section14Catalog 10 (⟨50,(15),[10],[46],1402⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1402,[5,6,8,9,10,12],1407⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid629 : RecordDataValid section14Catalog 10 (⟨53,(0),[9,10],[42],279⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨279,[1,2,3,4,5,6,7,8,9,10,11,12],280⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid630 : RecordDataValid section14Catalog 10 (⟨53,(0),[9,10],[46],325⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨325,[1,2,4,5,6,8,9,10,12],326⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid631 : RecordDataValid section14Catalog 10 (⟨53,(0),[9,10],[38],360⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨360,[1,2,3,4,5,6,7,8,9,10,12],361⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid632 : RecordDataValid section14Catalog 10 (⟨53,(1),[9,10],[42],280⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨280,[1,2,3,4,5,6,7,8,9,10,11,12],281⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid633 : RecordDataValid section14Catalog 10 (⟨53,(1),[9,10],[46],326⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨326,[1,2,4,5,6,8,9,10,12],327⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid634 : RecordDataValid section14Catalog 10 (⟨53,(1),[9,10],[38],361⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨361,[1,2,3,4,5,6,7,8,9,10,12],362⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid635 : RecordDataValid section14Catalog 10 (⟨53,(2),[9,10],[42],281⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨281,[1,2,3,4,5,6,7,8,9,10,11,12],282⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid636 : RecordDataValid section14Catalog 10 (⟨53,(2),[9,10],[46],327⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨327,[1,2,4,5,6,8,9,10,12],328⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid637 : RecordDataValid section14Catalog 10 (⟨53,(2),[9,10],[38],362⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨362,[1,2,3,4,5,6,7,8,9,10,12],363⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid638 : RecordDataValid section14Catalog 10 (⟨53,(3),[9,10],[42],282⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨282,[1,2,3,4,5,6,7,8,9,10,11,12],283⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid639 : RecordDataValid section14Catalog 10 (⟨53,(3),[9,10],[46],328⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨328,[1,2,4,5,6,8,9,10,12],329⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 608).take 32, section14RecordValid section14Catalog 10 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (10 ∈ r.states))).drop 608).take 32 = [⟨50,(9),[9,10],[42],302⟩,⟨50,(9),[9,10],[38],332⟩,⟨50,(9),[10],[46],1400⟩,⟨50,(10),[9,10],[42],303⟩,⟨50,(10),[9,10],[38],333⟩,⟨50,(10),[10],[46],1401⟩,⟨50,(11),[9,10],[42],304⟩,⟨50,(11),[9,10],[38],334⟩,⟨50,(11),[10],[46],1402⟩,⟨50,(12),[9,10],[42],301⟩,⟨50,(12),[9,10],[38],331⟩,⟨50,(12),[10],[46],1399⟩,⟨50,(13),[9,10],[42],302⟩,⟨50,(13),[9,10],[38],332⟩,⟨50,(13),[10],[46],1400⟩,⟨50,(14),[9,10],[42],306⟩,⟨50,(14),[9,10],[38],336⟩,⟨50,(14),[10],[46],1404⟩,⟨50,(15),[9,10],[42],304⟩,⟨50,(15),[9,10],[38],334⟩,⟨50,(15),[10],[46],1402⟩,⟨53,(0),[9,10],[42],279⟩,⟨53,(0),[9,10],[46],325⟩,⟨53,(0),[9,10],[38],360⟩,⟨53,(1),[9,10],[42],280⟩,⟨53,(1),[9,10],[46],326⟩,⟨53,(1),[9,10],[38],361⟩,⟨53,(2),[9,10],[42],281⟩,⟨53,(2),[9,10],[46],327⟩,⟨53,(2),[9,10],[38],362⟩,⟨53,(3),[9,10],[42],282⟩,⟨53,(3),[9,10],[46],328⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 10 _ hnum valid608
  · exact recordValid_of_data section14Catalog 10 _ hnum valid609
  · exact recordValid_of_data section14Catalog 10 _ hnum valid610
  · exact recordValid_of_data section14Catalog 10 _ hnum valid611
  · exact recordValid_of_data section14Catalog 10 _ hnum valid612
  · exact recordValid_of_data section14Catalog 10 _ hnum valid613
  · exact recordValid_of_data section14Catalog 10 _ hnum valid614
  · exact recordValid_of_data section14Catalog 10 _ hnum valid615
  · exact recordValid_of_data section14Catalog 10 _ hnum valid616
  · exact recordValid_of_data section14Catalog 10 _ hnum valid617
  · exact recordValid_of_data section14Catalog 10 _ hnum valid618
  · exact recordValid_of_data section14Catalog 10 _ hnum valid619
  · exact recordValid_of_data section14Catalog 10 _ hnum valid620
  · exact recordValid_of_data section14Catalog 10 _ hnum valid621
  · exact recordValid_of_data section14Catalog 10 _ hnum valid622
  · exact recordValid_of_data section14Catalog 10 _ hnum valid623
  · exact recordValid_of_data section14Catalog 10 _ hnum valid624
  · exact recordValid_of_data section14Catalog 10 _ hnum valid625
  · exact recordValid_of_data section14Catalog 10 _ hnum valid626
  · exact recordValid_of_data section14Catalog 10 _ hnum valid627
  · exact recordValid_of_data section14Catalog 10 _ hnum valid628
  · exact recordValid_of_data section14Catalog 10 _ hnum valid629
  · exact recordValid_of_data section14Catalog 10 _ hnum valid630
  · exact recordValid_of_data section14Catalog 10 _ hnum valid631
  · exact recordValid_of_data section14Catalog 10 _ hnum valid632
  · exact recordValid_of_data section14Catalog 10 _ hnum valid633
  · exact recordValid_of_data section14Catalog 10 _ hnum valid634
  · exact recordValid_of_data section14Catalog 10 _ hnum valid635
  · exact recordValid_of_data section14Catalog 10 _ hnum valid636
  · exact recordValid_of_data section14Catalog 10 _ hnum valid637
  · exact recordValid_of_data section14Catalog 10 _ hnum valid638
  · exact recordValid_of_data section14Catalog 10 _ hnum valid639
end Section14Records_10_608_640

#print axioms solution
