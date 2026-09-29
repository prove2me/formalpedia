-- Prove2me | solution 1 for Freiman.workReverse20260919_s0013_records_2624_2656
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T09:22:21.548707+00:00
-- url     : https://prove2.me/submissions/f22fc798-a8e5-48ce-976d-81a44399ca55

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
namespace Section14Records_13_2624_2656
private theorem valid2624 : RecordDataValid section14Catalog 13 (⟨230,(20),[1,2,5,6,13,14],[170],826⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨826,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],827⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2625 : RecordDataValid section14Catalog 13 (⟨230,(21),[1,2,5,6,13,14],[170],827⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨827,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],828⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2626 : RecordDataValid section14Catalog 13 (⟨230,(22),[1,2,5,6,13,14],[170],828⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨828,[1,2,3,5,6,7,10,11,13,14,15],829⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2627 : RecordDataValid section14Catalog 13 (⟨230,(23),[1,2,5,6,13,14],[170],829⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨829,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],830⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2628 : RecordDataValid section14Catalog 13 (⟨230,(24),[1,2,5,6,13,14],[170],828⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨828,[1,2,3,5,6,7,10,11,13,14,15],829⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2629 : RecordDataValid section14Catalog 13 (⟨231,(0),[1,2,5,6,13,14],[170],830⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨830,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],831⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2630 : RecordDataValid section14Catalog 13 (⟨231,(1),[1,2,5,6,13,14],[170],831⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨831,[1,2,3,4,5,6,7,10,11,13,14,15,16],832⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2631 : RecordDataValid section14Catalog 13 (⟨231,(2),[1,2,5,6,13,14],[170],832⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨832,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],833⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2632 : RecordDataValid section14Catalog 13 (⟨231,(3),[1,2,5,6,13,14],[170],833⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨833,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],834⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2633 : RecordDataValid section14Catalog 13 (⟨231,(4),[1,2,5,6,13,14],[170],830⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨830,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],831⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2634 : RecordDataValid section14Catalog 13 (⟨231,(5),[1,2,5,6,13,14],[170],831⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨831,[1,2,3,4,5,6,7,10,11,13,14,15,16],832⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2635 : RecordDataValid section14Catalog 13 (⟨231,(6),[1,2,5,6,13,14],[170],832⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨832,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],833⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2636 : RecordDataValid section14Catalog 13 (⟨231,(7),[1,2,5,6,13,14],[170],833⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨833,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],834⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2637 : RecordDataValid section14Catalog 13 (⟨231,(8),[1,2,5,6,13,14],[170],834⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨834,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],835⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2638 : RecordDataValid section14Catalog 13 (⟨231,(9),[1,2,5,6,13,14],[170],835⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨835,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],836⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2639 : RecordDataValid section14Catalog 13 (⟨231,(10),[1,2,5,6,13,14],[170],836⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨836,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],837⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2640 : RecordDataValid section14Catalog 13 (⟨231,(11),[1,2,5,6,13,14],[170],837⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨837,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],838⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2641 : RecordDataValid section14Catalog 13 (⟨231,(12),[1,2,5,6,13,14],[170],838⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨838,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],839⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2642 : RecordDataValid section14Catalog 13 (⟨231,(13),[1,2,5,6,13,14],[170],839⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨839,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],840⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2643 : RecordDataValid section14Catalog 13 (⟨231,(14),[1,2,5,6,13,14],[170],838⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨838,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],839⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2644 : RecordDataValid section14Catalog 13 (⟨231,(15),[1,2,5,6,13,14],[170],840⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨840,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],841⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2645 : RecordDataValid section14Catalog 13 (⟨231,(16),[1,2,5,6,13,14],[170],841⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨841,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],842⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2646 : RecordDataValid section14Catalog 13 (⟨231,(17),[1,2,5,6,13,14],[170],842⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨842,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],843⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2647 : RecordDataValid section14Catalog 13 (⟨231,(18),[1,2,5,6,13,14],[170],841⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨841,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],842⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2648 : RecordDataValid section14Catalog 13 (⟨231,(19),[1,2,5,6,13,14],[170],843⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨843,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],844⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2649 : RecordDataValid section14Catalog 13 (⟨232,(0),[1,2,5,6,13,14],[170],844⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨844,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],845⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2650 : RecordDataValid section14Catalog 13 (⟨232,(1),[1,2,5,6,13,14],[170],845⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨845,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],846⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2651 : RecordDataValid section14Catalog 13 (⟨232,(2),[1,2,5,6,13,14],[170],846⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨846,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],847⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2652 : RecordDataValid section14Catalog 13 (⟨232,(3),[1,2,5,6,13,14],[170],847⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨847,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],848⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2653 : RecordDataValid section14Catalog 13 (⟨232,(4),[1,5,6,13],[170],848⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨848,[1,4,5,6,8,9,10,11,12,13,16],849⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2654 : RecordDataValid section14Catalog 13 (⟨232,(5),[1,2,5,6,13,14],[170],849⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨849,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],850⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2655 : RecordDataValid section14Catalog 13 (⟨232,(6),[1,2,5,6,13,14],[170],850⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨850,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],851⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2624).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2624).take 32 = [⟨230,(20),[1,2,5,6,13,14],[170],826⟩,⟨230,(21),[1,2,5,6,13,14],[170],827⟩,⟨230,(22),[1,2,5,6,13,14],[170],828⟩,⟨230,(23),[1,2,5,6,13,14],[170],829⟩,⟨230,(24),[1,2,5,6,13,14],[170],828⟩,⟨231,(0),[1,2,5,6,13,14],[170],830⟩,⟨231,(1),[1,2,5,6,13,14],[170],831⟩,⟨231,(2),[1,2,5,6,13,14],[170],832⟩,⟨231,(3),[1,2,5,6,13,14],[170],833⟩,⟨231,(4),[1,2,5,6,13,14],[170],830⟩,⟨231,(5),[1,2,5,6,13,14],[170],831⟩,⟨231,(6),[1,2,5,6,13,14],[170],832⟩,⟨231,(7),[1,2,5,6,13,14],[170],833⟩,⟨231,(8),[1,2,5,6,13,14],[170],834⟩,⟨231,(9),[1,2,5,6,13,14],[170],835⟩,⟨231,(10),[1,2,5,6,13,14],[170],836⟩,⟨231,(11),[1,2,5,6,13,14],[170],837⟩,⟨231,(12),[1,2,5,6,13,14],[170],838⟩,⟨231,(13),[1,2,5,6,13,14],[170],839⟩,⟨231,(14),[1,2,5,6,13,14],[170],838⟩,⟨231,(15),[1,2,5,6,13,14],[170],840⟩,⟨231,(16),[1,2,5,6,13,14],[170],841⟩,⟨231,(17),[1,2,5,6,13,14],[170],842⟩,⟨231,(18),[1,2,5,6,13,14],[170],841⟩,⟨231,(19),[1,2,5,6,13,14],[170],843⟩,⟨232,(0),[1,2,5,6,13,14],[170],844⟩,⟨232,(1),[1,2,5,6,13,14],[170],845⟩,⟨232,(2),[1,2,5,6,13,14],[170],846⟩,⟨232,(3),[1,2,5,6,13,14],[170],847⟩,⟨232,(4),[1,5,6,13],[170],848⟩,⟨232,(5),[1,2,5,6,13,14],[170],849⟩,⟨232,(6),[1,2,5,6,13,14],[170],850⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2624
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2625
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2626
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2627
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2628
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2629
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2630
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2631
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2632
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2633
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2634
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2635
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2636
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2637
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2638
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2639
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2640
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2641
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2642
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2643
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2644
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2645
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2646
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2647
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2648
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2649
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2650
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2651
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2652
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2653
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2654
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2655
end Section14Records_13_2624_2656

#print axioms solution
