-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_2560_2624
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:15:32.988053+00:00
-- url     : https://prove2.me/submissions/57342f4a-95ae-4f1d-b6fb-a11d0e2a38e5

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2560_2592
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_2560_2592
private theorem valid2560 : RecordDataValid section14Catalog 6 (⟨180,(8),[5,6],[174],666⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨666,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],667⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2561 : RecordDataValid section14Catalog 6 (⟨180,(9),[1,2,5,6,13,14],[170],667⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨667,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],668⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2562 : RecordDataValid section14Catalog 6 (⟨180,(9),[5,6],[174],667⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨667,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],668⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2563 : RecordDataValid section14Catalog 6 (⟨180,(10),[1,2,5,6,13,14],[170],668⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨668,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],669⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2564 : RecordDataValid section14Catalog 6 (⟨180,(10),[5,6],[174],668⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨668,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],669⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2565 : RecordDataValid section14Catalog 6 (⟨180,(11),[1,2,5,6,13,14],[170],669⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨669,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],670⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2566 : RecordDataValid section14Catalog 6 (⟨180,(11),[5,6],[174],669⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨669,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],670⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2567 : RecordDataValid section14Catalog 6 (⟨180,(12),[1,2,5,6,13,14],[170],666⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨666,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],667⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2568 : RecordDataValid section14Catalog 6 (⟨180,(12),[5,6],[174],666⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨666,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],667⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2569 : RecordDataValid section14Catalog 6 (⟨180,(13),[1,2,5,6,13,14],[170],667⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨667,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],668⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2570 : RecordDataValid section14Catalog 6 (⟨180,(13),[5,6],[174],667⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨667,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],668⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2571 : RecordDataValid section14Catalog 6 (⟨180,(14),[1,2,5,6,13,14],[170],671⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨671,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],672⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2572 : RecordDataValid section14Catalog 6 (⟨180,(14),[5,6],[174],671⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨671,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],672⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2573 : RecordDataValid section14Catalog 6 (⟨180,(15),[1,2,5,6,13,14],[170],669⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨669,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],670⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2574 : RecordDataValid section14Catalog 6 (⟨180,(15),[5,6],[174],669⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨669,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],670⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2575 : RecordDataValid section14Catalog 6 (⟨183,(0),[1,2,5,6,13,14],[170],672⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨672,[1,2,3,5,6,7,10,11,13,14,15],673⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2576 : RecordDataValid section14Catalog 6 (⟨183,(0),[5,6],[174],989⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨989,[3,5,6,7],993⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2577 : RecordDataValid section14Catalog 6 (⟨183,(1),[1,2,5,6,13,14],[170],673⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨673,[1,2,3,5,6,7,10,11,13,14,15],674⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2578 : RecordDataValid section14Catalog 6 (⟨183,(1),[5,6],[174],990⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨990,[3,5,6,7],994⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2579 : RecordDataValid section14Catalog 6 (⟨183,(2),[1,2,5,6,13,14],[170],672⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨672,[1,2,3,5,6,7,10,11,13,14,15],673⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2580 : RecordDataValid section14Catalog 6 (⟨183,(2),[5,6],[174],989⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨989,[3,5,6,7],993⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2581 : RecordDataValid section14Catalog 6 (⟨183,(3),[1,2,5,6,13,14],[170],674⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨674,[1,2,3,5,6,7,10,11,13,14,15],675⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2582 : RecordDataValid section14Catalog 6 (⟨183,(3),[5,6],[174],991⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨991,[3,5,6,7],995⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2583 : RecordDataValid section14Catalog 6 (⟨183,(4),[1,2,5,6,13,14],[170],675⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨675,[1,2,3,5,6,7,10,11,13,14,15],676⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2584 : RecordDataValid section14Catalog 6 (⟨183,(4),[5,6],[174],992⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨992,[3,5,6,7],996⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2585 : RecordDataValid section14Catalog 6 (⟨183,(5),[1,2,5,6,13,14],[170],675⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨675,[1,2,3,5,6,7,10,11,13,14,15],676⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2586 : RecordDataValid section14Catalog 6 (⟨183,(5),[5,6],[174],992⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨992,[3,5,6,7],996⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2587 : RecordDataValid section14Catalog 6 (⟨183,(6),[1,2,5,6,13,14],[170],675⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨675,[1,2,3,5,6,7,10,11,13,14,15],676⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2588 : RecordDataValid section14Catalog 6 (⟨183,(6),[5,6],[174],992⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨992,[3,5,6,7],996⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2589 : RecordDataValid section14Catalog 6 (⟨183,(7),[1,2,5,6,13,14],[170],675⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨675,[1,2,3,5,6,7,10,11,13,14,15],676⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2590 : RecordDataValid section14Catalog 6 (⟨183,(7),[5,6],[174],992⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨992,[3,5,6,7],996⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2591 : RecordDataValid section14Catalog 6 (⟨183,(8),[1,2,5,6,13,14],[170],676⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨676,[1,2,3,5,6,7,10,11,13,14,15],677⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_2560_2592 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2560).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2560).take 32 = [⟨180,(8),[5,6],[174],666⟩,⟨180,(9),[1,2,5,6,13,14],[170],667⟩,⟨180,(9),[5,6],[174],667⟩,⟨180,(10),[1,2,5,6,13,14],[170],668⟩,⟨180,(10),[5,6],[174],668⟩,⟨180,(11),[1,2,5,6,13,14],[170],669⟩,⟨180,(11),[5,6],[174],669⟩,⟨180,(12),[1,2,5,6,13,14],[170],666⟩,⟨180,(12),[5,6],[174],666⟩,⟨180,(13),[1,2,5,6,13,14],[170],667⟩,⟨180,(13),[5,6],[174],667⟩,⟨180,(14),[1,2,5,6,13,14],[170],671⟩,⟨180,(14),[5,6],[174],671⟩,⟨180,(15),[1,2,5,6,13,14],[170],669⟩,⟨180,(15),[5,6],[174],669⟩,⟨183,(0),[1,2,5,6,13,14],[170],672⟩,⟨183,(0),[5,6],[174],989⟩,⟨183,(1),[1,2,5,6,13,14],[170],673⟩,⟨183,(1),[5,6],[174],990⟩,⟨183,(2),[1,2,5,6,13,14],[170],672⟩,⟨183,(2),[5,6],[174],989⟩,⟨183,(3),[1,2,5,6,13,14],[170],674⟩,⟨183,(3),[5,6],[174],991⟩,⟨183,(4),[1,2,5,6,13,14],[170],675⟩,⟨183,(4),[5,6],[174],992⟩,⟨183,(5),[1,2,5,6,13,14],[170],675⟩,⟨183,(5),[5,6],[174],992⟩,⟨183,(6),[1,2,5,6,13,14],[170],675⟩,⟨183,(6),[5,6],[174],992⟩,⟨183,(7),[1,2,5,6,13,14],[170],675⟩,⟨183,(7),[5,6],[174],992⟩,⟨183,(8),[1,2,5,6,13,14],[170],676⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2560
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2561
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2562
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2563
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2564
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2565
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2566
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2567
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2568
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2569
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2570
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2571
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2572
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2573
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2574
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2575
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2576
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2577
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2578
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2579
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2580
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2581
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2582
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2583
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2584
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2585
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2586
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2587
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2588
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2589
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2590
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2591
end Section14Records_6_2560_2592

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2560_2592


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2592_2624
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_2592_2624
private theorem valid2592 : RecordDataValid section14Catalog 6 (⟨183,(8),[5,6],[174],993⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨993,[3,5,6,7],997⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2593 : RecordDataValid section14Catalog 6 (⟨183,(9),[1,2,5,6,13,14],[170],676⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨676,[1,2,3,5,6,7,10,11,13,14,15],677⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2594 : RecordDataValid section14Catalog 6 (⟨183,(9),[5,6],[174],993⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨993,[3,5,6,7],997⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2595 : RecordDataValid section14Catalog 6 (⟨183,(10),[1,2,5,6,13,14],[170],676⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨676,[1,2,3,5,6,7,10,11,13,14,15],677⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2596 : RecordDataValid section14Catalog 6 (⟨183,(10),[5,6],[174],993⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨993,[3,5,6,7],997⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2597 : RecordDataValid section14Catalog 6 (⟨183,(11),[1,2,5,6,13,14],[170],676⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨676,[1,2,3,5,6,7,10,11,13,14,15],677⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2598 : RecordDataValid section14Catalog 6 (⟨183,(11),[5,6],[174],993⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨993,[3,5,6,7],997⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2599 : RecordDataValid section14Catalog 6 (⟨183,(12),[1,2,5,6,13,14],[170],677⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨677,[1,2,3,5,6,7,10,11,13,14,15],678⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2600 : RecordDataValid section14Catalog 6 (⟨183,(12),[5,6],[174],994⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨994,[3,5,6,7],998⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2601 : RecordDataValid section14Catalog 6 (⟨183,(13),[1,2,5,6,13,14],[170],677⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨677,[1,2,3,5,6,7,10,11,13,14,15],678⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2602 : RecordDataValid section14Catalog 6 (⟨183,(13),[5,6],[174],994⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨994,[3,5,6,7],998⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2603 : RecordDataValid section14Catalog 6 (⟨183,(14),[1,2,5,6,13,14],[170],677⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨677,[1,2,3,5,6,7,10,11,13,14,15],678⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2604 : RecordDataValid section14Catalog 6 (⟨183,(14),[5,6],[174],994⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨994,[3,5,6,7],998⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2605 : RecordDataValid section14Catalog 6 (⟨183,(15),[1,2,5,6,13,14],[170],677⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨677,[1,2,3,5,6,7,10,11,13,14,15],678⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2606 : RecordDataValid section14Catalog 6 (⟨183,(15),[5,6],[174],994⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨994,[3,5,6,7],998⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2607 : RecordDataValid section14Catalog 6 (⟨185,(0),[1,2,5,6,13,14],[170],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2608 : RecordDataValid section14Catalog 6 (⟨185,(0),[5,6],[174],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2609 : RecordDataValid section14Catalog 6 (⟨185,(1),[1,2,5,6,13,14],[170],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2610 : RecordDataValid section14Catalog 6 (⟨185,(1),[5,6],[174],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2611 : RecordDataValid section14Catalog 6 (⟨185,(2),[1,2,5,6,13,14],[170],680⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨680,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],681⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2612 : RecordDataValid section14Catalog 6 (⟨185,(2),[5,6],[174],680⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨680,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],681⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2613 : RecordDataValid section14Catalog 6 (⟨185,(3),[1,2,5,6,13,14],[170],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2614 : RecordDataValid section14Catalog 6 (⟨185,(3),[5,6],[174],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2615 : RecordDataValid section14Catalog 6 (⟨185,(4),[1,2,5,6,13,14],[170],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2616 : RecordDataValid section14Catalog 6 (⟨185,(4),[5,6],[174],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2617 : RecordDataValid section14Catalog 6 (⟨185,(5),[1,2,5,6,13,14],[170],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2618 : RecordDataValid section14Catalog 6 (⟨185,(5),[5,6],[174],679⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨679,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],680⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2619 : RecordDataValid section14Catalog 6 (⟨185,(6),[1,2,5,6,13,14],[170],682⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨682,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],683⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2620 : RecordDataValid section14Catalog 6 (⟨185,(6),[5,6],[174],682⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨682,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],683⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2621 : RecordDataValid section14Catalog 6 (⟨185,(7),[1,2,5,6,13,14],[170],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2622 : RecordDataValid section14Catalog 6 (⟨185,(7),[5,6],[174],681⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨681,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],682⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2623 : RecordDataValid section14Catalog 6 (⟨185,(8),[1,2,5,6,13,14],[170],678⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨678,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],679⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_2592_2624 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2592).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2592).take 32 = [⟨183,(8),[5,6],[174],993⟩,⟨183,(9),[1,2,5,6,13,14],[170],676⟩,⟨183,(9),[5,6],[174],993⟩,⟨183,(10),[1,2,5,6,13,14],[170],676⟩,⟨183,(10),[5,6],[174],993⟩,⟨183,(11),[1,2,5,6,13,14],[170],676⟩,⟨183,(11),[5,6],[174],993⟩,⟨183,(12),[1,2,5,6,13,14],[170],677⟩,⟨183,(12),[5,6],[174],994⟩,⟨183,(13),[1,2,5,6,13,14],[170],677⟩,⟨183,(13),[5,6],[174],994⟩,⟨183,(14),[1,2,5,6,13,14],[170],677⟩,⟨183,(14),[5,6],[174],994⟩,⟨183,(15),[1,2,5,6,13,14],[170],677⟩,⟨183,(15),[5,6],[174],994⟩,⟨185,(0),[1,2,5,6,13,14],[170],678⟩,⟨185,(0),[5,6],[174],678⟩,⟨185,(1),[1,2,5,6,13,14],[170],679⟩,⟨185,(1),[5,6],[174],679⟩,⟨185,(2),[1,2,5,6,13,14],[170],680⟩,⟨185,(2),[5,6],[174],680⟩,⟨185,(3),[1,2,5,6,13,14],[170],681⟩,⟨185,(3),[5,6],[174],681⟩,⟨185,(4),[1,2,5,6,13,14],[170],678⟩,⟨185,(4),[5,6],[174],678⟩,⟨185,(5),[1,2,5,6,13,14],[170],679⟩,⟨185,(5),[5,6],[174],679⟩,⟨185,(6),[1,2,5,6,13,14],[170],682⟩,⟨185,(6),[5,6],[174],682⟩,⟨185,(7),[1,2,5,6,13,14],[170],681⟩,⟨185,(7),[5,6],[174],681⟩,⟨185,(8),[1,2,5,6,13,14],[170],678⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2592
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2593
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2594
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2595
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2596
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2597
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2598
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2599
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2600
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2601
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2602
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2603
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2604
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2605
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2606
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2607
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2608
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2609
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2610
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2611
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2612
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2613
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2614
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2615
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2616
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2617
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2618
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2619
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2620
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2621
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2622
  · exact recordValid_of_data section14Catalog 6 _ hnum valid2623
end Section14Records_6_2592_2624

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_2592_2624

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 2560).take 64, section14RecordValid section14Catalog 6 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (6 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 6 r
  exact (all_of_interval_split P xs 2560 2592 2624 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_2560_2592 hnum) (Freiman.workReverse20260919_s0006_records_2592_2624 hnum))

#print axioms solution
