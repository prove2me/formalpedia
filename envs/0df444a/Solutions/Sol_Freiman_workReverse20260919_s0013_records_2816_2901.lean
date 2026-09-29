-- Prove2me | solution 1 for Freiman.workReverse20260919_s0013_records_2816_2901
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T09:02:17.808099+00:00
-- url     : https://prove2.me/submissions/f93060ad-046a-43c0-b34c-b367cf69b050

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2816_2848
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_2816_2848
private theorem valid2816 : RecordDataValid section14Catalog 13 (⟨249,(24),[1,2,5,6,13,14],[170],893⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨893,[1,2,3,4,5,6,7,8,13,14,15,16],895⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2817 : RecordDataValid section14Catalog 13 (⟨253,(0),[1,2,5,6,13,14],[170],884⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨884,[1,2,4,5,6,8,9,10,12,13,14,16],886⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2818 : RecordDataValid section14Catalog 13 (⟨253,(1),[1,2,5,6,13,14],[170],894⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨894,[1,2,4,5,6,8,9,10,13,14,16],896⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2819 : RecordDataValid section14Catalog 13 (⟨253,(2),[1,2,5,6,13,14],[170],895⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨895,[1,2,3,4,5,6,7,8,9,10,13,14,16],897⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2820 : RecordDataValid section14Catalog 13 (⟨253,(3),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2821 : RecordDataValid section14Catalog 13 (⟨253,(4),[1,2,5,6,13,14],[170],30⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨30,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],30⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2822 : RecordDataValid section14Catalog 13 (⟨253,(5),[1,2,5,6,13,14],[170],884⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨884,[1,2,4,5,6,8,9,10,12,13,14,16],886⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2823 : RecordDataValid section14Catalog 13 (⟨253,(6),[1,2,5,6,13,14],[170],894⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨894,[1,2,4,5,6,8,9,10,13,14,16],896⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2824 : RecordDataValid section14Catalog 13 (⟨253,(7),[1,2,5,6,13,14],[170],896⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨896,[1,2,4,5,6,10,13,14,16],898⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2825 : RecordDataValid section14Catalog 13 (⟨253,(8),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2826 : RecordDataValid section14Catalog 13 (⟨253,(9),[1,2,5,6,13,14],[170],32⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨32,[1,2,4,5,6,8,9,10,12,13,14,16],32⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2827 : RecordDataValid section14Catalog 13 (⟨253,(10),[1,2,5,6,13,14],[170],84⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2828 : RecordDataValid section14Catalog 13 (⟨253,(11),[1,2,5,6,13,14],[170],897⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨897,[1,2,4,5,6,8,9,10,12,13,14,16],899⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2829 : RecordDataValid section14Catalog 13 (⟨253,(12),[1,2,5,6,13,14],[170],898⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨898,[1,2,4,5,6,8,9,10,12,13,14,16],900⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2830 : RecordDataValid section14Catalog 13 (⟨253,(13),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2831 : RecordDataValid section14Catalog 13 (⟨253,(14),[1,2,5,6,13,14],[170],34⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨34,[1,2,4,5,6,8,9,10,12,13,14,16],34⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2832 : RecordDataValid section14Catalog 13 (⟨253,(15),[1,2,5,6,13,14],[170],35⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2833 : RecordDataValid section14Catalog 13 (⟨253,(16),[1,2,5,6,13,14],[170],36⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨36,[1,2,4,5,6,8,9,10,12,13,14,16],36⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2834 : RecordDataValid section14Catalog 13 (⟨253,(17),[1,2,5,6,13,14],[170],37⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨37,[1,2,4,5,6,8,9,10,12,13,14,16],37⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2835 : RecordDataValid section14Catalog 13 (⟨253,(18),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2836 : RecordDataValid section14Catalog 13 (⟨253,(19),[1,2,5,6,13,14],[170],37⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨37,[1,2,4,5,6,8,9,10,12,13,14,16],37⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2837 : RecordDataValid section14Catalog 13 (⟨253,(20),[1,2,5,6,13,14],[170],38⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2838 : RecordDataValid section14Catalog 13 (⟨253,(21),[1,2,5,6,13,14],[170],39⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨39,[1,2,4,5,6,8,9,10,12,13,14,16],39⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2839 : RecordDataValid section14Catalog 13 (⟨253,(22),[1,2,5,6,13,14],[170],40⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨40,[1,2,4,5,6,8,9,10,12,13,14,16],40⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2840 : RecordDataValid section14Catalog 13 (⟨253,(23),[1,2,5,6,13,14],[170],29⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2841 : RecordDataValid section14Catalog 13 (⟨253,(24),[1,2,5,6,13,14],[170],40⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨40,[1,2,4,5,6,8,9,10,12,13,14,16],40⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2842 : RecordDataValid section14Catalog 13 (⟨258,(5),[6,13],[170],105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨105,[1,2,3,5,6,7,13,14,15],105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2843 : RecordDataValid section14Catalog 13 (⟨258,(7),[1,2,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2844 : RecordDataValid section14Catalog 13 (⟨258,(8),[1,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2845 : RecordDataValid section14Catalog 13 (⟨258,(9),[5,6,13,14],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2846 : RecordDataValid section14Catalog 13 (⟨258,(15),[5,13],[170],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2847 : RecordDataValid section14Catalog 13 (⟨258,(16),[1,5,6,13,14],[170],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_2816_2848 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2816).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2816).take 32 = [⟨249,(24),[1,2,5,6,13,14],[170],893⟩,⟨253,(0),[1,2,5,6,13,14],[170],884⟩,⟨253,(1),[1,2,5,6,13,14],[170],894⟩,⟨253,(2),[1,2,5,6,13,14],[170],895⟩,⟨253,(3),[1,2,5,6,13,14],[170],29⟩,⟨253,(4),[1,2,5,6,13,14],[170],30⟩,⟨253,(5),[1,2,5,6,13,14],[170],884⟩,⟨253,(6),[1,2,5,6,13,14],[170],894⟩,⟨253,(7),[1,2,5,6,13,14],[170],896⟩,⟨253,(8),[1,2,5,6,13,14],[170],29⟩,⟨253,(9),[1,2,5,6,13,14],[170],32⟩,⟨253,(10),[1,2,5,6,13,14],[170],84⟩,⟨253,(11),[1,2,5,6,13,14],[170],897⟩,⟨253,(12),[1,2,5,6,13,14],[170],898⟩,⟨253,(13),[1,2,5,6,13,14],[170],29⟩,⟨253,(14),[1,2,5,6,13,14],[170],34⟩,⟨253,(15),[1,2,5,6,13,14],[170],35⟩,⟨253,(16),[1,2,5,6,13,14],[170],36⟩,⟨253,(17),[1,2,5,6,13,14],[170],37⟩,⟨253,(18),[1,2,5,6,13,14],[170],29⟩,⟨253,(19),[1,2,5,6,13,14],[170],37⟩,⟨253,(20),[1,2,5,6,13,14],[170],38⟩,⟨253,(21),[1,2,5,6,13,14],[170],39⟩,⟨253,(22),[1,2,5,6,13,14],[170],40⟩,⟨253,(23),[1,2,5,6,13,14],[170],29⟩,⟨253,(24),[1,2,5,6,13,14],[170],40⟩,⟨258,(5),[6,13],[170],105⟩,⟨258,(7),[1,2,5,6,13,14],[170],3⟩,⟨258,(8),[1,5,6,13,14],[170],3⟩,⟨258,(9),[5,6,13,14],[170],143⟩,⟨258,(15),[5,13],[170],48⟩,⟨258,(16),[1,5,6,13,14],[170],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2816
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2817
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2818
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2819
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2820
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2821
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2822
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2823
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2824
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2825
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2826
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2827
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2828
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2829
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2830
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2831
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2832
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2833
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2834
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2835
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2836
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2837
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2838
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2839
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2840
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2841
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2842
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2843
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2844
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2845
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2846
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2847
end Section14Records_13_2816_2848

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2816_2848


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2848_2880
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_2848_2880
private theorem valid2848 : RecordDataValid section14Catalog 13 (⟨258,(17),[1,2,5,6,13,14],[170],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2849 : RecordDataValid section14Catalog 13 (⟨258,(19),[1,13],[170],48⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨48,[1,2,3,5,6,7,13,14,15],48⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2850 : RecordDataValid section14Catalog 13 (⟨260,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2851 : RecordDataValid section14Catalog 13 (⟨260,(-1),[1,2,5,6,9,10,13,14],[1,5],881⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨881,[1,2,3,5,6,7,9,10,11,13,14,15],883⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2852 : RecordDataValid section14Catalog 13 (⟨260,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2853 : RecordDataValid section14Catalog 13 (⟨260,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2854 : RecordDataValid section14Catalog 13 (⟨260,(-1),[1,2,5,6,13,14],[17,21,41,45,57,61],881⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨881,[1,2,3,5,6,7,9,10,11,13,14,15],883⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2855 : RecordDataValid section14Catalog 13 (⟨260,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],882⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2856 : RecordDataValid section14Catalog 13 (⟨260,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],883⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨883,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],885⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2857 : RecordDataValid section14Catalog 13 (⟨260,(-1),[1,2,5,6,13,14],[130,134],884⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨884,[1,2,4,5,6,8,9,10,12,13,14,16],886⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2858 : RecordDataValid section14Catalog 13 (⟨260,(-1),[1,2,5,6,13,14],[146],885⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨885,[1,2,3,5,6,7,13,14,15],887⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2859 : RecordDataValid section14Catalog 13 (⟨260,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],886⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨886,[1,2,4,5,6,8,9,10,12,13,14,16],888⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2860 : RecordDataValid section14Catalog 13 (⟨260,(-1),[1,2,5,6,13,14],[150],887⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨887,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],889⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2861 : RecordDataValid section14Catalog 13 (⟨260,(-1),[1,2,5,6,13,14],[174],908⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨908,[1,2,3,5,6,7,13,14,15],910⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2862 : RecordDataValid section14Catalog 13 (⟨260,(-1),[1,2,5,6,13,14],[186],909⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨909,[1,2,4,5,6,8,9,10,12,13,14,16],911⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2863 : RecordDataValid section14Catalog 13 (⟨260,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],910⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨910,[1,2,3,5,6,7,9,10,11,13,14,15],912⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2864 : RecordDataValid section14Catalog 13 (⟨260,(-1),[1,2,6,13,14],[170],911⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨911,[1,2,4,13,14,16],913⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2865 : RecordDataValid section14Catalog 13 (⟨260,(-1),[1,2,13,14],[131,135],884⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨884,[1,2,4,5,6,8,9,10,12,13,14,16],886⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2866 : RecordDataValid section14Catalog 13 (⟨260,(-1),[1,5,6,13],[194,198],910⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨910,[1,2,3,5,6,7,9,10,11,13,14,15],912⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2867 : RecordDataValid section14Catalog 13 (⟨260,(-1),[1,5,9,13],[0,4],881⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨881,[1,2,3,5,6,7,9,10,11,13,14,15],883⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2868 : RecordDataValid section14Catalog 13 (⟨260,(-1),[1,5,13],[16,20,40,44,56,60],881⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨881,[1,2,3,5,6,7,9,10,11,13,14,15],883⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2869 : RecordDataValid section14Catalog 13 (⟨260,(-1),[1,5,13],[195,199,211,215,235,239,251,255],910⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨910,[1,2,3,5,6,7,9,10,11,13,14,15],912⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2870 : RecordDataValid section14Catalog 13 (⟨260,(-1),[9,10,13],[10,11,14,15,26,27,30,31],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2871 : RecordDataValid section14Catalog 13 (⟨260,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2872 : RecordDataValid section14Catalog 13 (⟨260,(-1),[13],[190],908⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨908,[1,2,3,5,6,7,13,14,15],910⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2873 : RecordDataValid section14Catalog 13 (⟨636,(0),[13,14],[170],1724⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1724,[13,14,15,16],1729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2874 : RecordDataValid section14Catalog 13 (⟨636,(1),[13,14],[170],1724⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1724,[13,14,15,16],1729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2875 : RecordDataValid section14Catalog 13 (⟨636,(2),[13,14],[170],1725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1725,[13,14,15,16],1730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2876 : RecordDataValid section14Catalog 13 (⟨636,(3),[13,14],[170],1725⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1725,[13,14,15,16],1730⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2877 : RecordDataValid section14Catalog 13 (⟨636,(4),[13,14],[170],1724⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1724,[13,14,15,16],1729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2878 : RecordDataValid section14Catalog 13 (⟨636,(5),[13,14],[170],1724⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1724,[13,14,15,16],1729⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2879 : RecordDataValid section14Catalog 13 (⟨636,(6),[13,14],[170],1726⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1726,[13,14,15,16],1731⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_2848_2880 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2848).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2848).take 32 = [⟨258,(17),[1,2,5,6,13,14],[170],48⟩,⟨258,(19),[1,13],[170],48⟩,⟨260,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩,⟨260,(-1),[1,2,5,6,9,10,13,14],[1,5],881⟩,⟨260,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩,⟨260,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩,⟨260,(-1),[1,2,5,6,13,14],[17,21,41,45,57,61],881⟩,⟨260,(-1),[1,2,5,6,13,14],[64,68,80,84,104,108,120,124],882⟩,⟨260,(-1),[1,2,5,6,13,14],[65,69,81,85,105,109,121,125],883⟩,⟨260,(-1),[1,2,5,6,13,14],[130,134],884⟩,⟨260,(-1),[1,2,5,6,13,14],[146],885⟩,⟨260,(-1),[1,2,5,6,13,14],[147,151,171,175,187,191],886⟩,⟨260,(-1),[1,2,5,6,13,14],[150],887⟩,⟨260,(-1),[1,2,5,6,13,14],[174],908⟩,⟨260,(-1),[1,2,5,6,13,14],[186],909⟩,⟨260,(-1),[1,2,5,6,13,14],[210,214,234,238,250,254],910⟩,⟨260,(-1),[1,2,6,13,14],[170],911⟩,⟨260,(-1),[1,2,13,14],[131,135],884⟩,⟨260,(-1),[1,5,6,13],[194,198],910⟩,⟨260,(-1),[1,5,9,13],[0,4],881⟩,⟨260,(-1),[1,5,13],[16,20,40,44,56,60],881⟩,⟨260,(-1),[1,5,13],[195,199,211,215,235,239,251,255],910⟩,⟨260,(-1),[9,10,13],[10,11,14,15,26,27,30,31],2⟩,⟨260,(-1),[13],[34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],2⟩,⟨260,(-1),[13],[190],908⟩,⟨636,(0),[13,14],[170],1724⟩,⟨636,(1),[13,14],[170],1724⟩,⟨636,(2),[13,14],[170],1725⟩,⟨636,(3),[13,14],[170],1725⟩,⟨636,(4),[13,14],[170],1724⟩,⟨636,(5),[13,14],[170],1724⟩,⟨636,(6),[13,14],[170],1726⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2848
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2849
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2850
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2851
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2852
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2853
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2854
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2855
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2856
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2857
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2858
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2859
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2860
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2861
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2862
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2863
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2864
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2865
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2866
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2867
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2868
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2869
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2870
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2871
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2872
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2873
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2874
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2875
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2876
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2877
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2878
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2879
end Section14Records_13_2848_2880

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2848_2880


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2880_2901
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_2880_2901
private theorem valid2880 : RecordDataValid section14Catalog 13 (⟨636,(7),[13,14],[170],1726⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1726,[13,14,15,16],1731⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2881 : RecordDataValid section14Catalog 13 (⟨636,(8),[13,14],[170],47⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨47,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],47⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2882 : RecordDataValid section14Catalog 13 (⟨636,(9),[13,14],[170],47⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨47,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],47⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2883 : RecordDataValid section14Catalog 13 (⟨639,(1),[13],[170],621⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨621,[1,4,5,6,8,9,10,12,13,16],622⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2884 : RecordDataValid section14Catalog 13 (⟨639,(3),[13],[170],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2885 : RecordDataValid section14Catalog 13 (⟨639,(6),[13],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2886 : RecordDataValid section14Catalog 13 (⟨639,(8),[13],[170],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2887 : RecordDataValid section14Catalog 13 (⟨640,(1),[13,14],[170],872⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨872,[1,2,4,5,6,8,9,10,12,13,14,16],873⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2888 : RecordDataValid section14Catalog 13 (⟨640,(3),[13,14],[170],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2889 : RecordDataValid section14Catalog 13 (⟨640,(6),[13,14],[170],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2890 : RecordDataValid section14Catalog 13 (⟨640,(8),[13,14],[170],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2891 : RecordDataValid section14Catalog 13 (⟨643,(0),[13,14],[170],1729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1729,[13,14,16],1734⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2892 : RecordDataValid section14Catalog 13 (⟨643,(1),[13,14],[170],1729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1729,[13,14,16],1734⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2893 : RecordDataValid section14Catalog 13 (⟨643,(2),[13,14],[170],1730⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1730,[13,14,16],1735⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2894 : RecordDataValid section14Catalog 13 (⟨643,(3),[13,14],[170],1730⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1730,[13,14,16],1735⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2895 : RecordDataValid section14Catalog 13 (⟨643,(4),[13,14],[170],1729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1729,[13,14,16],1734⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2896 : RecordDataValid section14Catalog 13 (⟨643,(5),[13,14],[170],1729⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1729,[13,14,16],1734⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2897 : RecordDataValid section14Catalog 13 (⟨643,(6),[13,14],[170],1731⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1731,[13,14,16],1736⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2898 : RecordDataValid section14Catalog 13 (⟨643,(7),[13,14],[170],1731⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1731,[13,14,16],1736⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2899 : RecordDataValid section14Catalog 13 (⟨643,(8),[13,14],[170],905⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨905,[1,2,4,5,6,8,9,10,12,13,14,16],907⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2900 : RecordDataValid section14Catalog 13 (⟨643,(9),[13,14],[170],905⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨905,[1,2,4,5,6,8,9,10,12,13,14,16],907⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_2880_2901 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2880).take 21, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2880).take 21 = [⟨636,(7),[13,14],[170],1726⟩,⟨636,(8),[13,14],[170],47⟩,⟨636,(9),[13,14],[170],47⟩,⟨639,(1),[13],[170],621⟩,⟨639,(3),[13],[170],101⟩,⟨639,(6),[13],[170],143⟩,⟨639,(8),[13],[170],101⟩,⟨640,(1),[13,14],[170],872⟩,⟨640,(3),[13,14],[170],101⟩,⟨640,(6),[13,14],[170],143⟩,⟨640,(8),[13,14],[170],101⟩,⟨643,(0),[13,14],[170],1729⟩,⟨643,(1),[13,14],[170],1729⟩,⟨643,(2),[13,14],[170],1730⟩,⟨643,(3),[13,14],[170],1730⟩,⟨643,(4),[13,14],[170],1729⟩,⟨643,(5),[13,14],[170],1729⟩,⟨643,(6),[13,14],[170],1731⟩,⟨643,(7),[13,14],[170],1731⟩,⟨643,(8),[13,14],[170],905⟩,⟨643,(9),[13,14],[170],905⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2880
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2881
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2882
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2883
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2884
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2885
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2886
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2887
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2888
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2889
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2890
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2891
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2892
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2893
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2894
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2895
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2896
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2897
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2898
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2899
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2900
end Section14Records_13_2880_2901

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2880_2901

open Freiman
namespace M7Section14Sep18
universe u

theorem all_of_take_drop {α : Type u} (P : α → Prop) (xs : List α) (n : ℕ)
    (ht : ∀ x ∈ xs.take n, P x) (hd : ∀ x ∈ xs.drop n, P x) :
    ∀ x ∈ xs, P x := by
  intro x hx
  have hm : x ∈ xs.take n ++ xs.drop n := by
    simpa only [List.take_append_drop] using hx
  rcases List.mem_append.mp hm with h | h
  · exact ht x h
  · exact hd x h

theorem all_of_chunks {α : Type u} (P : α → Prop) (xs : List α) (lo size : ℕ)
    (ht : ∀ x ∈ (xs.drop lo).take size, P x)
    (hd : ∀ x ∈ xs.drop (lo+size), P x) : ∀ x ∈ xs.drop lo, P x := by
  apply all_of_take_drop P (xs.drop lo) size ht
  simpa only [List.drop_drop] using hd

theorem all_empty {α : Type u} (P : α → Prop) (xs : List α) (h : xs = []) :
    ∀ x ∈ xs, P x := by
  rw [h]
  exact fun x hx => False.elim (List.not_mem_nil hx)
end M7Section14Sep18

namespace M7Section14Sep18
universe u

theorem all_of_interval_split {α : Type u} (P : α → Prop) (xs : List α)
    (lo cut hi : ℕ) (hc : lo ≤ cut) (hh : cut ≤ hi)
    (left : ∀ x ∈ (xs.drop lo).take (cut-lo), P x)
    (right : ∀ x ∈ (xs.drop cut).take (hi-cut), P x) :
    ∀ x ∈ (xs.drop lo).take (hi-lo), P x := by
  have hsum : hi-lo = (cut-lo)+(hi-cut) := by omega
  have hdrop : lo+(cut-lo) = cut := by omega
  rw [hsum, List.take_add, List.drop_drop, hdrop]
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact left x hx
  · exact right x hx
end M7Section14Sep18

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2816).take 85, section14RecordValid section14Catalog 13 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (13 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 13 r
  exact (all_of_interval_split P xs 2816 2848 2901 (by decide) (by decide) (Freiman.workReverse20260919_s0013_records_2816_2848 hnum) (all_of_interval_split P xs 2848 2880 2901 (by decide) (by decide) (Freiman.workReverse20260919_s0013_records_2848_2880 hnum) (Freiman.workReverse20260919_s0013_records_2880_2901 hnum)))

#print axioms solution
