-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_3680_3712
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:04:37.492913+00:00
-- url     : https://prove2.me/submissions/bce3e279-c9c0-4069-9edd-0b14aa45dc1e

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
namespace Section14Records_5_3680_3712
private theorem valid3680 : RecordDataValid section14Catalog 5 (⟨226,(5),[1,2,5,6,13,14],[170],770⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨770,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],771⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3681 : RecordDataValid section14Catalog 5 (⟨226,(5),[5,6],[174],770⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨770,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],771⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3682 : RecordDataValid section14Catalog 5 (⟨226,(6),[1,2,5,6,13,14],[170],771⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨771,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],772⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3683 : RecordDataValid section14Catalog 5 (⟨226,(6),[5,6],[174],771⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨771,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],772⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3684 : RecordDataValid section14Catalog 5 (⟨226,(7),[1,2,5,6,13,14],[170],771⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨771,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],772⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3685 : RecordDataValid section14Catalog 5 (⟨226,(7),[5,6],[174],771⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨771,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],772⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3686 : RecordDataValid section14Catalog 5 (⟨226,(8),[1,2,5,6,13,14],[170],772⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨772,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],773⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3687 : RecordDataValid section14Catalog 5 (⟨226,(8),[5,6],[174],772⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨772,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],773⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3688 : RecordDataValid section14Catalog 5 (⟨226,(9),[1,2,5,6,13,14],[170],772⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨772,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],773⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3689 : RecordDataValid section14Catalog 5 (⟨226,(9),[5,6],[174],772⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨772,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],773⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3690 : RecordDataValid section14Catalog 5 (⟨227,(0),[1,2,5,6,13,14],[170],773⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨773,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],774⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3691 : RecordDataValid section14Catalog 5 (⟨227,(0),[5,6],[174],773⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨773,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],774⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3692 : RecordDataValid section14Catalog 5 (⟨227,(1),[1,2,5,6,13,14],[170],774⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨774,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],775⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3693 : RecordDataValid section14Catalog 5 (⟨227,(1),[5,6],[174],774⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨774,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],775⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3694 : RecordDataValid section14Catalog 5 (⟨227,(2),[1,2,5,6,13,14],[170],775⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨775,[1,2,3,5,6,7,10,11,13,14,15],776⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3695 : RecordDataValid section14Catalog 5 (⟨227,(2),[5,6],[174],1056⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1056,[3,5,6,7],1060⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3696 : RecordDataValid section14Catalog 5 (⟨227,(3),[1,2,5,6,13,14],[170],776⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨776,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],777⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3697 : RecordDataValid section14Catalog 5 (⟨227,(3),[5,6],[174],1057⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1057,[3,5,6,7],1061⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3698 : RecordDataValid section14Catalog 5 (⟨227,(4),[1,2,5,6,13,14],[170],775⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨775,[1,2,3,5,6,7,10,11,13,14,15],776⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3699 : RecordDataValid section14Catalog 5 (⟨227,(4),[5,6],[174],1056⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1056,[3,5,6,7],1060⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3700 : RecordDataValid section14Catalog 5 (⟨227,(5),[1,2,5,6,13,14],[170],773⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨773,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],774⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3701 : RecordDataValid section14Catalog 5 (⟨227,(5),[5,6],[174],773⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨773,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],774⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3702 : RecordDataValid section14Catalog 5 (⟨227,(6),[1,2,5,6,13,14],[170],774⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨774,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],775⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3703 : RecordDataValid section14Catalog 5 (⟨227,(6),[5,6],[174],774⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨774,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],775⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3704 : RecordDataValid section14Catalog 5 (⟨227,(7),[1,2,5,6,13,14],[170],775⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨775,[1,2,3,5,6,7,10,11,13,14,15],776⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3705 : RecordDataValid section14Catalog 5 (⟨227,(7),[5,6],[174],1056⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1056,[3,5,6,7],1060⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3706 : RecordDataValid section14Catalog 5 (⟨227,(8),[1,2,5,6,13,14],[170],776⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨776,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],777⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3707 : RecordDataValid section14Catalog 5 (⟨227,(8),[5,6],[174],1057⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1057,[3,5,6,7],1061⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3708 : RecordDataValid section14Catalog 5 (⟨227,(9),[1,2,5,6,13,14],[170],775⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨775,[1,2,3,5,6,7,10,11,13,14,15],776⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3709 : RecordDataValid section14Catalog 5 (⟨227,(9),[5,6],[174],1056⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1056,[3,5,6,7],1060⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3710 : RecordDataValid section14Catalog 5 (⟨227,(10),[1,2,5,6,13,14],[170],777⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨777,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],778⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3711 : RecordDataValid section14Catalog 5 (⟨227,(10),[5,6],[174],777⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨777,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],778⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3680).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3680).take 32 = [⟨226,(5),[1,2,5,6,13,14],[170],770⟩,⟨226,(5),[5,6],[174],770⟩,⟨226,(6),[1,2,5,6,13,14],[170],771⟩,⟨226,(6),[5,6],[174],771⟩,⟨226,(7),[1,2,5,6,13,14],[170],771⟩,⟨226,(7),[5,6],[174],771⟩,⟨226,(8),[1,2,5,6,13,14],[170],772⟩,⟨226,(8),[5,6],[174],772⟩,⟨226,(9),[1,2,5,6,13,14],[170],772⟩,⟨226,(9),[5,6],[174],772⟩,⟨227,(0),[1,2,5,6,13,14],[170],773⟩,⟨227,(0),[5,6],[174],773⟩,⟨227,(1),[1,2,5,6,13,14],[170],774⟩,⟨227,(1),[5,6],[174],774⟩,⟨227,(2),[1,2,5,6,13,14],[170],775⟩,⟨227,(2),[5,6],[174],1056⟩,⟨227,(3),[1,2,5,6,13,14],[170],776⟩,⟨227,(3),[5,6],[174],1057⟩,⟨227,(4),[1,2,5,6,13,14],[170],775⟩,⟨227,(4),[5,6],[174],1056⟩,⟨227,(5),[1,2,5,6,13,14],[170],773⟩,⟨227,(5),[5,6],[174],773⟩,⟨227,(6),[1,2,5,6,13,14],[170],774⟩,⟨227,(6),[5,6],[174],774⟩,⟨227,(7),[1,2,5,6,13,14],[170],775⟩,⟨227,(7),[5,6],[174],1056⟩,⟨227,(8),[1,2,5,6,13,14],[170],776⟩,⟨227,(8),[5,6],[174],1057⟩,⟨227,(9),[1,2,5,6,13,14],[170],775⟩,⟨227,(9),[5,6],[174],1056⟩,⟨227,(10),[1,2,5,6,13,14],[170],777⟩,⟨227,(10),[5,6],[174],777⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3680
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3681
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3682
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3683
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3684
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3685
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3686
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3687
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3688
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3689
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3690
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3691
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3692
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3693
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3694
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3695
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3696
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3697
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3698
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3699
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3700
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3701
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3702
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3703
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3704
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3705
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3706
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3707
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3708
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3709
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3710
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3711
end Section14Records_5_3680_3712

#print axioms solution
