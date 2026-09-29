-- Prove2me | solution 1 for Freiman.section14_s0009_records_0672_0704
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T20:11:42.642711+00:00
-- url     : https://prove2.me/submissions/5c78e5fb-0c0b-47fc-8fd4-38fb2e77e081

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
namespace Section14Records_9_672_704
private theorem valid672 : RecordDataValid section14Catalog 9 (⟨55,(10),[9,10],[38],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid673 : RecordDataValid section14Catalog 9 (⟨55,(10),[9,10],[46],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid674 : RecordDataValid section14Catalog 9 (⟨55,(10),[9,10],[42],97⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨97,[1,2,5,6,9,10,13,14],97⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid675 : RecordDataValid section14Catalog 9 (⟨55,(11),[9,10],[38],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid676 : RecordDataValid section14Catalog 9 (⟨55,(11),[9,10],[42],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid677 : RecordDataValid section14Catalog 9 (⟨55,(11),[9,10],[46],234⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨234,[1,2,5,6,9,10,13,14],234⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid678 : RecordDataValid section14Catalog 9 (⟨55,(12),[9],[38],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid679 : RecordDataValid section14Catalog 9 (⟨55,(12),[9],[42,46],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid680 : RecordDataValid section14Catalog 9 (⟨55,(13),[9],[42,46],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid681 : RecordDataValid section14Catalog 9 (⟨55,(13),[9,10],[38],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid682 : RecordDataValid section14Catalog 9 (⟨55,(14),[9,10],[38],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid683 : RecordDataValid section14Catalog 9 (⟨55,(14),[9,10],[46],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid684 : RecordDataValid section14Catalog 9 (⟨55,(14),[9,10],[42],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid685 : RecordDataValid section14Catalog 9 (⟨55,(15),[9,10],[38],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid686 : RecordDataValid section14Catalog 9 (⟨55,(15),[9,10],[42],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid687 : RecordDataValid section14Catalog 9 (⟨55,(15),[9,10],[46],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid688 : RecordDataValid section14Catalog 9 (⟨57,(0),[9,10],[38,42,46],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid689 : RecordDataValid section14Catalog 9 (⟨57,(1),[9,10],[38,42,46],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid690 : RecordDataValid section14Catalog 9 (⟨57,(2),[9],[46],337⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨337,[1,2,3,4,5,6,7,8,9,10,11,12],338⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid691 : RecordDataValid section14Catalog 9 (⟨57,(2),[9,10],[42],311⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨311,[1,2,4,5,6,8,9,10,12],312⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid692 : RecordDataValid section14Catalog 9 (⟨57,(2),[9,10],[38],337⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨337,[1,2,3,4,5,6,7,8,9,10,11,12],338⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid693 : RecordDataValid section14Catalog 9 (⟨57,(3),[9,10],[38,42,46],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid694 : RecordDataValid section14Catalog 9 (⟨57,(4),[9,10],[38,42,46],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid695 : RecordDataValid section14Catalog 9 (⟨57,(5),[9,10],[38,42,46],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid696 : RecordDataValid section14Catalog 9 (⟨57,(6),[9],[46],338⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨338,[1,2,4,5,6,8,9,10,12],339⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid697 : RecordDataValid section14Catalog 9 (⟨57,(6),[9,10],[42],284⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨284,[1,2,4,5,6,8,9,10,12],285⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid698 : RecordDataValid section14Catalog 9 (⟨57,(6),[9,10],[38],338⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨338,[1,2,4,5,6,8,9,10,12],339⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid699 : RecordDataValid section14Catalog 9 (⟨57,(7),[9,10],[38,42,46],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid700 : RecordDataValid section14Catalog 9 (⟨57,(8),[9,10],[38,42,46],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid701 : RecordDataValid section14Catalog 9 (⟨57,(9),[9,10],[38,42,46],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid702 : RecordDataValid section14Catalog 9 (⟨57,(10),[9],[46],339⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨339,[1,2,4,5,6,8,9,10,12],340⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid703 : RecordDataValid section14Catalog 9 (⟨57,(10),[9,10],[42],285⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨285,[1,2,4,5,6,8,9,10,12],286⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 672).take 32, section14RecordValid section14Catalog 9 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (9 ∈ r.states))).drop 672).take 32 = [⟨55,(10),[9,10],[38],3⟩,⟨55,(10),[9,10],[46],29⟩,⟨55,(10),[9,10],[42],97⟩,⟨55,(11),[9,10],[38],3⟩,⟨55,(11),[9,10],[42],29⟩,⟨55,(11),[9,10],[46],234⟩,⟨55,(12),[9],[38],98⟩,⟨55,(12),[9],[42,46],99⟩,⟨55,(13),[9],[42,46],99⟩,⟨55,(13),[9,10],[38],99⟩,⟨55,(14),[9,10],[38],3⟩,⟨55,(14),[9,10],[46],29⟩,⟨55,(14),[9,10],[42],99⟩,⟨55,(15),[9,10],[38],3⟩,⟨55,(15),[9,10],[42],29⟩,⟨55,(15),[9,10],[46],99⟩,⟨57,(0),[9,10],[38,42,46],2⟩,⟨57,(1),[9,10],[38,42,46],2⟩,⟨57,(2),[9],[46],337⟩,⟨57,(2),[9,10],[42],311⟩,⟨57,(2),[9,10],[38],337⟩,⟨57,(3),[9,10],[38,42,46],101⟩,⟨57,(4),[9,10],[38,42,46],2⟩,⟨57,(5),[9,10],[38,42,46],2⟩,⟨57,(6),[9],[46],338⟩,⟨57,(6),[9,10],[42],284⟩,⟨57,(6),[9,10],[38],338⟩,⟨57,(7),[9,10],[38,42,46],101⟩,⟨57,(8),[9,10],[38,42,46],2⟩,⟨57,(9),[9,10],[38,42,46],2⟩,⟨57,(10),[9],[46],339⟩,⟨57,(10),[9,10],[42],285⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 9 _ hnum valid672
  · exact recordValid_of_data section14Catalog 9 _ hnum valid673
  · exact recordValid_of_data section14Catalog 9 _ hnum valid674
  · exact recordValid_of_data section14Catalog 9 _ hnum valid675
  · exact recordValid_of_data section14Catalog 9 _ hnum valid676
  · exact recordValid_of_data section14Catalog 9 _ hnum valid677
  · exact recordValid_of_data section14Catalog 9 _ hnum valid678
  · exact recordValid_of_data section14Catalog 9 _ hnum valid679
  · exact recordValid_of_data section14Catalog 9 _ hnum valid680
  · exact recordValid_of_data section14Catalog 9 _ hnum valid681
  · exact recordValid_of_data section14Catalog 9 _ hnum valid682
  · exact recordValid_of_data section14Catalog 9 _ hnum valid683
  · exact recordValid_of_data section14Catalog 9 _ hnum valid684
  · exact recordValid_of_data section14Catalog 9 _ hnum valid685
  · exact recordValid_of_data section14Catalog 9 _ hnum valid686
  · exact recordValid_of_data section14Catalog 9 _ hnum valid687
  · exact recordValid_of_data section14Catalog 9 _ hnum valid688
  · exact recordValid_of_data section14Catalog 9 _ hnum valid689
  · exact recordValid_of_data section14Catalog 9 _ hnum valid690
  · exact recordValid_of_data section14Catalog 9 _ hnum valid691
  · exact recordValid_of_data section14Catalog 9 _ hnum valid692
  · exact recordValid_of_data section14Catalog 9 _ hnum valid693
  · exact recordValid_of_data section14Catalog 9 _ hnum valid694
  · exact recordValid_of_data section14Catalog 9 _ hnum valid695
  · exact recordValid_of_data section14Catalog 9 _ hnum valid696
  · exact recordValid_of_data section14Catalog 9 _ hnum valid697
  · exact recordValid_of_data section14Catalog 9 _ hnum valid698
  · exact recordValid_of_data section14Catalog 9 _ hnum valid699
  · exact recordValid_of_data section14Catalog 9 _ hnum valid700
  · exact recordValid_of_data section14Catalog 9 _ hnum valid701
  · exact recordValid_of_data section14Catalog 9 _ hnum valid702
  · exact recordValid_of_data section14Catalog 9 _ hnum valid703
end Section14Records_9_672_704

#print axioms solution
