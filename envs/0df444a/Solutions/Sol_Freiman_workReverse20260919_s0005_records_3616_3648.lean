-- Prove2me | solution 1 for Freiman.workReverse20260919_s0005_records_3616_3648
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:03:50.264471+00:00
-- url     : https://prove2.me/submissions/ba1233a6-707a-43af-b403-089578b9e9ec

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
namespace Section14Records_5_3616_3648
private theorem valid3616 : RecordDataValid section14Catalog 5 (⟨224,(23),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3617 : RecordDataValid section14Catalog 5 (⟨224,(23),[5,6],[174],1038⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1038,[3,5,6,7],1042⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3618 : RecordDataValid section14Catalog 5 (⟨224,(24),[1,2,5,6,13,14],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3619 : RecordDataValid section14Catalog 5 (⟨224,(24),[5,6],[174],1039⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1039,[3,5,6,7],1043⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3620 : RecordDataValid section14Catalog 5 (⟨225,(0),[1,2,5,6,13,14],[170],747⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨747,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],748⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3621 : RecordDataValid section14Catalog 5 (⟨225,(0),[5,6],[174],747⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨747,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],748⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3622 : RecordDataValid section14Catalog 5 (⟨225,(1),[1,2,5,6,13,14],[170],748⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨748,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],749⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3623 : RecordDataValid section14Catalog 5 (⟨225,(1),[5,6],[174],748⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨748,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],749⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3624 : RecordDataValid section14Catalog 5 (⟨225,(2),[1,2,5,6,13,14],[170],749⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨749,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],750⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3625 : RecordDataValid section14Catalog 5 (⟨225,(2),[5,6],[174],749⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨749,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],750⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3626 : RecordDataValid section14Catalog 5 (⟨225,(3),[1,2,5,6,13,14],[170],750⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨750,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],751⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3627 : RecordDataValid section14Catalog 5 (⟨225,(3),[5,6],[174],750⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨750,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],751⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3628 : RecordDataValid section14Catalog 5 (⟨225,(4),[1,2,5,6,13,14],[170],749⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨749,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],750⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3629 : RecordDataValid section14Catalog 5 (⟨225,(4),[5,6],[174],749⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨749,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],750⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3630 : RecordDataValid section14Catalog 5 (⟨225,(5),[1,2,5,6,13,14],[170],751⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨751,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],752⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3631 : RecordDataValid section14Catalog 5 (⟨225,(5),[5,6],[174],751⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨751,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],752⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3632 : RecordDataValid section14Catalog 5 (⟨225,(6),[1,2,5,6,13,14],[170],752⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨752,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],753⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3633 : RecordDataValid section14Catalog 5 (⟨225,(6),[5,6],[174],752⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨752,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],753⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3634 : RecordDataValid section14Catalog 5 (⟨225,(7),[1,2,5,6,13,14],[170],753⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨753,[1,2,3,5,6,7,10,11,13,14,15],754⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3635 : RecordDataValid section14Catalog 5 (⟨225,(7),[5,6],[174],1051⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1051,[3,5,6,7],1055⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3636 : RecordDataValid section14Catalog 5 (⟨225,(8),[1,2,5,6,13,14],[170],754⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨754,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],755⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3637 : RecordDataValid section14Catalog 5 (⟨225,(8),[5,6],[174],754⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨754,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],755⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3638 : RecordDataValid section14Catalog 5 (⟨225,(9),[1,2,5,6,13,14],[170],753⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨753,[1,2,3,5,6,7,10,11,13,14,15],754⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3639 : RecordDataValid section14Catalog 5 (⟨225,(9),[5,6],[174],1051⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1051,[3,5,6,7],1055⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3640 : RecordDataValid section14Catalog 5 (⟨225,(10),[1,2,5,6,13,14],[170],755⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨755,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],756⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3641 : RecordDataValid section14Catalog 5 (⟨225,(10),[5,6],[174],755⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨755,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],756⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3642 : RecordDataValid section14Catalog 5 (⟨225,(11),[1,2,5,6,13,14],[170],756⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨756,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],757⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3643 : RecordDataValid section14Catalog 5 (⟨225,(11),[5,6],[174],756⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨756,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],757⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3644 : RecordDataValid section14Catalog 5 (⟨225,(12),[1,2,5,6,13,14],[170],757⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨757,[1,2,3,5,6,7,10,11,13,14,15],758⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3645 : RecordDataValid section14Catalog 5 (⟨225,(12),[5,6],[174],1053⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1053,[3,5,6,7],1057⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3646 : RecordDataValid section14Catalog 5 (⟨225,(13),[1,2,5,6,13,14],[170],758⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨758,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],759⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3647 : RecordDataValid section14Catalog 5 (⟨225,(13),[5,6],[174],758⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨758,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],759⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3616).take 32, section14RecordValid section14Catalog 5 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (5 ∈ r.states))).drop 3616).take 32 = [⟨224,(23),[1,2,5,6,13,14],[170],517⟩,⟨224,(23),[5,6],[174],1038⟩,⟨224,(24),[1,2,5,6,13,14],[170],518⟩,⟨224,(24),[5,6],[174],1039⟩,⟨225,(0),[1,2,5,6,13,14],[170],747⟩,⟨225,(0),[5,6],[174],747⟩,⟨225,(1),[1,2,5,6,13,14],[170],748⟩,⟨225,(1),[5,6],[174],748⟩,⟨225,(2),[1,2,5,6,13,14],[170],749⟩,⟨225,(2),[5,6],[174],749⟩,⟨225,(3),[1,2,5,6,13,14],[170],750⟩,⟨225,(3),[5,6],[174],750⟩,⟨225,(4),[1,2,5,6,13,14],[170],749⟩,⟨225,(4),[5,6],[174],749⟩,⟨225,(5),[1,2,5,6,13,14],[170],751⟩,⟨225,(5),[5,6],[174],751⟩,⟨225,(6),[1,2,5,6,13,14],[170],752⟩,⟨225,(6),[5,6],[174],752⟩,⟨225,(7),[1,2,5,6,13,14],[170],753⟩,⟨225,(7),[5,6],[174],1051⟩,⟨225,(8),[1,2,5,6,13,14],[170],754⟩,⟨225,(8),[5,6],[174],754⟩,⟨225,(9),[1,2,5,6,13,14],[170],753⟩,⟨225,(9),[5,6],[174],1051⟩,⟨225,(10),[1,2,5,6,13,14],[170],755⟩,⟨225,(10),[5,6],[174],755⟩,⟨225,(11),[1,2,5,6,13,14],[170],756⟩,⟨225,(11),[5,6],[174],756⟩,⟨225,(12),[1,2,5,6,13,14],[170],757⟩,⟨225,(12),[5,6],[174],1053⟩,⟨225,(13),[1,2,5,6,13,14],[170],758⟩,⟨225,(13),[5,6],[174],758⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3616
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3617
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3618
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3619
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3620
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3621
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3622
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3623
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3624
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3625
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3626
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3627
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3628
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3629
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3630
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3631
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3632
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3633
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3634
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3635
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3636
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3637
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3638
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3639
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3640
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3641
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3642
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3643
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3644
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3645
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3646
  · exact recordValid_of_data section14Catalog 5 _ hnum valid3647
end Section14Records_5_3616_3648

#print axioms solution
