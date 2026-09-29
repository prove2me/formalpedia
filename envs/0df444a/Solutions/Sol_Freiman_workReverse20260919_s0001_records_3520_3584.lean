-- Prove2me | solution 1 for Freiman.workReverse20260919_s0001_records_3520_3584
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T03:26:23.545463+00:00
-- url     : https://prove2.me/submissions/56d9c555-b1f1-4903-964b-379621710774

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3520_3552
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_3520_3552
private theorem valid3520 : RecordDataValid section14Catalog 1 (⟨224,(1),[1,2,5,6,13,14],[170],539⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨539,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],540⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3521 : RecordDataValid section14Catalog 1 (⟨224,(2),[1,2,5,6,13,14],[170],540⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨540,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],541⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3522 : RecordDataValid section14Catalog 1 (⟨224,(3),[1,2,5,6,13,14],[170],541⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨541,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],542⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3523 : RecordDataValid section14Catalog 1 (⟨224,(4),[1,2,5,6,13,14],[170],542⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨542,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],543⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3524 : RecordDataValid section14Catalog 1 (⟨224,(5),[1,2,5,6,13,14],[170],543⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨543,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],544⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3525 : RecordDataValid section14Catalog 1 (⟨224,(6),[1,2,5,6,13,14],[170],543⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨543,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],544⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3526 : RecordDataValid section14Catalog 1 (⟨224,(7),[1,2,5,6,13,14],[170],544⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨544,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],545⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3527 : RecordDataValid section14Catalog 1 (⟨224,(8),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3528 : RecordDataValid section14Catalog 1 (⟨224,(9),[1,2,5,6,13,14],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3529 : RecordDataValid section14Catalog 1 (⟨224,(10),[1,2,5,6,13,14],[170],545⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨545,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],546⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3530 : RecordDataValid section14Catalog 1 (⟨224,(11),[1,2,5,6,13,14],[170],545⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨545,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],546⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3531 : RecordDataValid section14Catalog 1 (⟨224,(12),[1,2,5,6,13,14],[170],544⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨544,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],545⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3532 : RecordDataValid section14Catalog 1 (⟨224,(13),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3533 : RecordDataValid section14Catalog 1 (⟨224,(14),[1,2,5,6,13,14],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3534 : RecordDataValid section14Catalog 1 (⟨224,(15),[1,2,5,6,13,14],[170],546⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨546,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],547⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3535 : RecordDataValid section14Catalog 1 (⟨224,(16),[1,2,5,6,13,14],[170],546⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨546,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],547⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3536 : RecordDataValid section14Catalog 1 (⟨224,(17),[1,2,5,6,13,14],[170],544⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨544,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],545⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3537 : RecordDataValid section14Catalog 1 (⟨224,(18),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3538 : RecordDataValid section14Catalog 1 (⟨224,(19),[1,2,5,6,13,14],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3539 : RecordDataValid section14Catalog 1 (⟨224,(20),[1,2,5,6,13,14],[170],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3540 : RecordDataValid section14Catalog 1 (⟨224,(21),[1,2,5,6,13,14],[170],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3541 : RecordDataValid section14Catalog 1 (⟨224,(22),[1,2,5,6,13,14],[170],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3542 : RecordDataValid section14Catalog 1 (⟨224,(23),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3543 : RecordDataValid section14Catalog 1 (⟨224,(24),[1,2,5,6,13,14],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3544 : RecordDataValid section14Catalog 1 (⟨225,(0),[1,2,5,6,13,14],[170],747⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨747,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],748⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3545 : RecordDataValid section14Catalog 1 (⟨225,(1),[1,2,5,6,13,14],[170],748⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨748,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],749⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3546 : RecordDataValid section14Catalog 1 (⟨225,(2),[1,2,5,6,13,14],[170],749⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨749,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],750⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3547 : RecordDataValid section14Catalog 1 (⟨225,(3),[1,2,5,6,13,14],[170],750⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨750,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],751⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3548 : RecordDataValid section14Catalog 1 (⟨225,(4),[1,2,5,6,13,14],[170],749⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨749,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],750⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3549 : RecordDataValid section14Catalog 1 (⟨225,(5),[1,2,5,6,13,14],[170],751⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨751,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],752⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3550 : RecordDataValid section14Catalog 1 (⟨225,(6),[1,2,5,6,13,14],[170],752⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨752,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],753⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3551 : RecordDataValid section14Catalog 1 (⟨225,(7),[1,2,5,6,13,14],[170],753⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨753,[1,2,3,5,6,7,10,11,13,14,15],754⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_3520_3552 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3520).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3520).take 32 = [⟨224,(1),[1,2,5,6,13,14],[170],539⟩,⟨224,(2),[1,2,5,6,13,14],[170],540⟩,⟨224,(3),[1,2,5,6,13,14],[170],541⟩,⟨224,(4),[1,2,5,6,13,14],[170],542⟩,⟨224,(5),[1,2,5,6,13,14],[170],543⟩,⟨224,(6),[1,2,5,6,13,14],[170],543⟩,⟨224,(7),[1,2,5,6,13,14],[170],544⟩,⟨224,(8),[1,2,5,6,13,14],[170],517⟩,⟨224,(9),[1,2,5,6,13,14],[170],518⟩,⟨224,(10),[1,2,5,6,13,14],[170],545⟩,⟨224,(11),[1,2,5,6,13,14],[170],545⟩,⟨224,(12),[1,2,5,6,13,14],[170],544⟩,⟨224,(13),[1,2,5,6,13,14],[170],517⟩,⟨224,(14),[1,2,5,6,13,14],[170],518⟩,⟨224,(15),[1,2,5,6,13,14],[170],546⟩,⟨224,(16),[1,2,5,6,13,14],[170],546⟩,⟨224,(17),[1,2,5,6,13,14],[170],544⟩,⟨224,(18),[1,2,5,6,13,14],[170],517⟩,⟨224,(19),[1,2,5,6,13,14],[170],518⟩,⟨224,(20),[1,2,5,6,13,14],[170],547⟩,⟨224,(21),[1,2,5,6,13,14],[170],547⟩,⟨224,(22),[1,2,5,6,13,14],[170],547⟩,⟨224,(23),[1,2,5,6,13,14],[170],517⟩,⟨224,(24),[1,2,5,6,13,14],[170],518⟩,⟨225,(0),[1,2,5,6,13,14],[170],747⟩,⟨225,(1),[1,2,5,6,13,14],[170],748⟩,⟨225,(2),[1,2,5,6,13,14],[170],749⟩,⟨225,(3),[1,2,5,6,13,14],[170],750⟩,⟨225,(4),[1,2,5,6,13,14],[170],749⟩,⟨225,(5),[1,2,5,6,13,14],[170],751⟩,⟨225,(6),[1,2,5,6,13,14],[170],752⟩,⟨225,(7),[1,2,5,6,13,14],[170],753⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3520
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3521
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3522
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3523
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3524
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3525
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3526
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3527
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3528
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3529
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3530
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3531
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3532
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3533
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3534
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3535
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3536
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3537
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3538
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3539
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3540
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3541
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3542
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3543
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3544
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3545
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3546
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3547
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3548
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3549
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3550
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3551
end Section14Records_1_3520_3552

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3520_3552


namespace WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3552_3584
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_1_3552_3584
private theorem valid3552 : RecordDataValid section14Catalog 1 (⟨225,(8),[1,2,5,6,13,14],[170],754⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨754,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],755⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3553 : RecordDataValid section14Catalog 1 (⟨225,(9),[1,2,5,6,13,14],[170],753⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨753,[1,2,3,5,6,7,10,11,13,14,15],754⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3554 : RecordDataValid section14Catalog 1 (⟨225,(10),[1,2,5,6,13,14],[170],755⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨755,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],756⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3555 : RecordDataValid section14Catalog 1 (⟨225,(11),[1,2,5,6,13,14],[170],756⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨756,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],757⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3556 : RecordDataValid section14Catalog 1 (⟨225,(12),[1,2,5,6,13,14],[170],757⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨757,[1,2,3,5,6,7,10,11,13,14,15],758⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3557 : RecordDataValid section14Catalog 1 (⟨225,(13),[1,2,5,6,13,14],[170],758⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨758,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],759⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3558 : RecordDataValid section14Catalog 1 (⟨225,(14),[1,2,5,6,13,14],[170],757⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨757,[1,2,3,5,6,7,10,11,13,14,15],758⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3559 : RecordDataValid section14Catalog 1 (⟨225,(15),[1,2,5,6,13,14],[170],759⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨759,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],760⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3560 : RecordDataValid section14Catalog 1 (⟨225,(16),[1,2,5,6,13,14],[170],760⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨760,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],761⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3561 : RecordDataValid section14Catalog 1 (⟨225,(17),[1,2,5,6,13,14],[170],761⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨761,[1,2,3,5,6,7,10,11,13,14,15],762⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3562 : RecordDataValid section14Catalog 1 (⟨225,(18),[1,2,5,6,13,14],[170],762⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨762,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],763⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3563 : RecordDataValid section14Catalog 1 (⟨225,(19),[1,2,5,6,13,14],[170],761⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨761,[1,2,3,5,6,7,10,11,13,14,15],762⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3564 : RecordDataValid section14Catalog 1 (⟨225,(20),[1,2,5,6,13,14],[170],763⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨763,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],764⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3565 : RecordDataValid section14Catalog 1 (⟨225,(21),[1,2,5,6,13,14],[170],764⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨764,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],765⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3566 : RecordDataValid section14Catalog 1 (⟨225,(22),[1,2,5,6,13,14],[170],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3567 : RecordDataValid section14Catalog 1 (⟨225,(23),[1,2,5,6,13,14],[170],765⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨765,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],766⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3568 : RecordDataValid section14Catalog 1 (⟨225,(24),[1,2,5,6,13,14],[170],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3569 : RecordDataValid section14Catalog 1 (⟨226,(0),[1,2,5,6,13,14],[170],766⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨766,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],767⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3570 : RecordDataValid section14Catalog 1 (⟨226,(1),[1,2,5,6,13,14],[170],767⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨767,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],768⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3571 : RecordDataValid section14Catalog 1 (⟨226,(2),[1,2,5,6,13,14],[170],768⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨768,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],769⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3572 : RecordDataValid section14Catalog 1 (⟨226,(3),[1,2,5,6,13,14],[170],767⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨767,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],768⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3573 : RecordDataValid section14Catalog 1 (⟨226,(4),[1,2,5,6,13,14],[170],769⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨769,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],770⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3574 : RecordDataValid section14Catalog 1 (⟨226,(5),[1,2,5,6,13,14],[170],770⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨770,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],771⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3575 : RecordDataValid section14Catalog 1 (⟨226,(6),[1,2,5,6,13,14],[170],771⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨771,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],772⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3576 : RecordDataValid section14Catalog 1 (⟨226,(7),[1,2,5,6,13,14],[170],771⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨771,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],772⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3577 : RecordDataValid section14Catalog 1 (⟨226,(8),[1,2,5,6,13,14],[170],772⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨772,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],773⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3578 : RecordDataValid section14Catalog 1 (⟨226,(9),[1,2,5,6,13,14],[170],772⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨772,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],773⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3579 : RecordDataValid section14Catalog 1 (⟨227,(0),[1,2,5,6,13,14],[170],773⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨773,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],774⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3580 : RecordDataValid section14Catalog 1 (⟨227,(1),[1,2,5,6,13,14],[170],774⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨774,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],775⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3581 : RecordDataValid section14Catalog 1 (⟨227,(2),[1,2,5,6,13,14],[170],775⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨775,[1,2,3,5,6,7,10,11,13,14,15],776⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3582 : RecordDataValid section14Catalog 1 (⟨227,(3),[1,2,5,6,13,14],[170],776⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨776,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],777⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3583 : RecordDataValid section14Catalog 1 (⟨227,(4),[1,2,5,6,13,14],[170],775⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨775,[1,2,3,5,6,7,10,11,13,14,15],776⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0001_records_3552_3584 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3552).take 32, section14RecordValid section14Catalog 1 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3552).take 32 = [⟨225,(8),[1,2,5,6,13,14],[170],754⟩,⟨225,(9),[1,2,5,6,13,14],[170],753⟩,⟨225,(10),[1,2,5,6,13,14],[170],755⟩,⟨225,(11),[1,2,5,6,13,14],[170],756⟩,⟨225,(12),[1,2,5,6,13,14],[170],757⟩,⟨225,(13),[1,2,5,6,13,14],[170],758⟩,⟨225,(14),[1,2,5,6,13,14],[170],757⟩,⟨225,(15),[1,2,5,6,13,14],[170],759⟩,⟨225,(16),[1,2,5,6,13,14],[170],760⟩,⟨225,(17),[1,2,5,6,13,14],[170],761⟩,⟨225,(18),[1,2,5,6,13,14],[170],762⟩,⟨225,(19),[1,2,5,6,13,14],[170],761⟩,⟨225,(20),[1,2,5,6,13,14],[170],763⟩,⟨225,(21),[1,2,5,6,13,14],[170],764⟩,⟨225,(22),[1,2,5,6,13,14],[170],547⟩,⟨225,(23),[1,2,5,6,13,14],[170],765⟩,⟨225,(24),[1,2,5,6,13,14],[170],547⟩,⟨226,(0),[1,2,5,6,13,14],[170],766⟩,⟨226,(1),[1,2,5,6,13,14],[170],767⟩,⟨226,(2),[1,2,5,6,13,14],[170],768⟩,⟨226,(3),[1,2,5,6,13,14],[170],767⟩,⟨226,(4),[1,2,5,6,13,14],[170],769⟩,⟨226,(5),[1,2,5,6,13,14],[170],770⟩,⟨226,(6),[1,2,5,6,13,14],[170],771⟩,⟨226,(7),[1,2,5,6,13,14],[170],771⟩,⟨226,(8),[1,2,5,6,13,14],[170],772⟩,⟨226,(9),[1,2,5,6,13,14],[170],772⟩,⟨227,(0),[1,2,5,6,13,14],[170],773⟩,⟨227,(1),[1,2,5,6,13,14],[170],774⟩,⟨227,(2),[1,2,5,6,13,14],[170],775⟩,⟨227,(3),[1,2,5,6,13,14],[170],776⟩,⟨227,(4),[1,2,5,6,13,14],[170],775⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3552
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3553
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3554
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3555
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3556
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3557
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3558
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3559
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3560
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3561
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3562
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3563
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3564
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3565
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3566
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3567
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3568
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3569
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3570
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3571
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3572
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3573
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3574
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3575
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3576
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3577
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3578
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3579
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3580
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3581
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3582
  · exact recordValid_of_data section14Catalog 1 _ hnum valid3583
end Section14Records_1_3552_3584

end WorkReverseInterface_Freiman_workReverse20260919_s0001_records_3552_3584

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (1 ∈ r.states))).drop 3520).take 64, section14RecordValid section14Catalog 1 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (1 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 1 r
  exact (all_of_interval_split P xs 3520 3552 3584 (by decide) (by decide) (Freiman.workReverse20260919_s0001_records_3520_3552 hnum) (Freiman.workReverse20260919_s0001_records_3552_3584 hnum))

#print axioms solution
