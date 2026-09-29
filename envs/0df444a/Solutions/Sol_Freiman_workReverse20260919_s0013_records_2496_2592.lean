-- Prove2me | solution 1 for Freiman.workReverse20260919_s0013_records_2496_2592
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T09:00:37.670918+00:00
-- url     : https://prove2.me/submissions/c2d6f89b-6918-4694-b003-f30b3b3d3afa

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2496_2528
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_2496_2528
private theorem valid2496 : RecordDataValid section14Catalog 13 (⟨224,(2),[1,2,5,6,13,14],[170],540⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨540,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],541⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2497 : RecordDataValid section14Catalog 13 (⟨224,(3),[1,2,5,6,13,14],[170],541⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨541,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],542⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2498 : RecordDataValid section14Catalog 13 (⟨224,(4),[1,2,5,6,13,14],[170],542⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨542,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],543⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2499 : RecordDataValid section14Catalog 13 (⟨224,(5),[1,2,5,6,13,14],[170],543⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨543,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],544⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2500 : RecordDataValid section14Catalog 13 (⟨224,(6),[1,2,5,6,13,14],[170],543⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨543,[1,2,3,4,5,6,7,9,10,11,13,14,15,16],544⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2501 : RecordDataValid section14Catalog 13 (⟨224,(7),[1,2,5,6,13,14],[170],544⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨544,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],545⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2502 : RecordDataValid section14Catalog 13 (⟨224,(8),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2503 : RecordDataValid section14Catalog 13 (⟨224,(9),[1,2,5,6,13,14],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2504 : RecordDataValid section14Catalog 13 (⟨224,(10),[1,2,5,6,13,14],[170],545⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨545,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],546⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2505 : RecordDataValid section14Catalog 13 (⟨224,(11),[1,2,5,6,13,14],[170],545⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨545,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],546⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2506 : RecordDataValid section14Catalog 13 (⟨224,(12),[1,2,5,6,13,14],[170],544⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨544,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],545⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2507 : RecordDataValid section14Catalog 13 (⟨224,(13),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2508 : RecordDataValid section14Catalog 13 (⟨224,(14),[1,2,5,6,13,14],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2509 : RecordDataValid section14Catalog 13 (⟨224,(15),[1,2,5,6,13,14],[170],546⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨546,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],547⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2510 : RecordDataValid section14Catalog 13 (⟨224,(16),[1,2,5,6,13,14],[170],546⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨546,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],547⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2511 : RecordDataValid section14Catalog 13 (⟨224,(17),[1,2,5,6,13,14],[170],544⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨544,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],545⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2512 : RecordDataValid section14Catalog 13 (⟨224,(18),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2513 : RecordDataValid section14Catalog 13 (⟨224,(19),[1,2,5,6,13,14],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2514 : RecordDataValid section14Catalog 13 (⟨224,(20),[1,2,5,6,13,14],[170],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2515 : RecordDataValid section14Catalog 13 (⟨224,(21),[1,2,5,6,13,14],[170],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2516 : RecordDataValid section14Catalog 13 (⟨224,(22),[1,2,5,6,13,14],[170],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2517 : RecordDataValid section14Catalog 13 (⟨224,(23),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2518 : RecordDataValid section14Catalog 13 (⟨224,(24),[1,2,5,6,13,14],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2519 : RecordDataValid section14Catalog 13 (⟨225,(0),[1,2,5,6,13,14],[170],747⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨747,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],748⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2520 : RecordDataValid section14Catalog 13 (⟨225,(1),[1,2,5,6,13,14],[170],748⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨748,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],749⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2521 : RecordDataValid section14Catalog 13 (⟨225,(2),[1,2,5,6,13,14],[170],749⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨749,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],750⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2522 : RecordDataValid section14Catalog 13 (⟨225,(3),[1,2,5,6,13,14],[170],750⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨750,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],751⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2523 : RecordDataValid section14Catalog 13 (⟨225,(4),[1,2,5,6,13,14],[170],749⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨749,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],750⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2524 : RecordDataValid section14Catalog 13 (⟨225,(5),[1,2,5,6,13,14],[170],751⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨751,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],752⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2525 : RecordDataValid section14Catalog 13 (⟨225,(6),[1,2,5,6,13,14],[170],752⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨752,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],753⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2526 : RecordDataValid section14Catalog 13 (⟨225,(7),[1,2,5,6,13,14],[170],753⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨753,[1,2,3,5,6,7,10,11,13,14,15],754⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2527 : RecordDataValid section14Catalog 13 (⟨225,(8),[1,2,5,6,13,14],[170],754⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨754,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],755⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_2496_2528 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2496).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2496).take 32 = [⟨224,(2),[1,2,5,6,13,14],[170],540⟩,⟨224,(3),[1,2,5,6,13,14],[170],541⟩,⟨224,(4),[1,2,5,6,13,14],[170],542⟩,⟨224,(5),[1,2,5,6,13,14],[170],543⟩,⟨224,(6),[1,2,5,6,13,14],[170],543⟩,⟨224,(7),[1,2,5,6,13,14],[170],544⟩,⟨224,(8),[1,2,5,6,13,14],[170],517⟩,⟨224,(9),[1,2,5,6,13,14],[170],518⟩,⟨224,(10),[1,2,5,6,13,14],[170],545⟩,⟨224,(11),[1,2,5,6,13,14],[170],545⟩,⟨224,(12),[1,2,5,6,13,14],[170],544⟩,⟨224,(13),[1,2,5,6,13,14],[170],517⟩,⟨224,(14),[1,2,5,6,13,14],[170],518⟩,⟨224,(15),[1,2,5,6,13,14],[170],546⟩,⟨224,(16),[1,2,5,6,13,14],[170],546⟩,⟨224,(17),[1,2,5,6,13,14],[170],544⟩,⟨224,(18),[1,2,5,6,13,14],[170],517⟩,⟨224,(19),[1,2,5,6,13,14],[170],518⟩,⟨224,(20),[1,2,5,6,13,14],[170],547⟩,⟨224,(21),[1,2,5,6,13,14],[170],547⟩,⟨224,(22),[1,2,5,6,13,14],[170],547⟩,⟨224,(23),[1,2,5,6,13,14],[170],517⟩,⟨224,(24),[1,2,5,6,13,14],[170],518⟩,⟨225,(0),[1,2,5,6,13,14],[170],747⟩,⟨225,(1),[1,2,5,6,13,14],[170],748⟩,⟨225,(2),[1,2,5,6,13,14],[170],749⟩,⟨225,(3),[1,2,5,6,13,14],[170],750⟩,⟨225,(4),[1,2,5,6,13,14],[170],749⟩,⟨225,(5),[1,2,5,6,13,14],[170],751⟩,⟨225,(6),[1,2,5,6,13,14],[170],752⟩,⟨225,(7),[1,2,5,6,13,14],[170],753⟩,⟨225,(8),[1,2,5,6,13,14],[170],754⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2496
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2497
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2498
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2499
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2500
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2501
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2502
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2503
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2504
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2505
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2506
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2507
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2508
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2509
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2510
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2511
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2512
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2513
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2514
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2515
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2516
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2517
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2518
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2519
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2520
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2521
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2522
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2523
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2524
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2525
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2526
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2527
end Section14Records_13_2496_2528

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2496_2528


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2528_2560
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_2528_2560
private theorem valid2528 : RecordDataValid section14Catalog 13 (⟨225,(9),[1,2,5,6,13,14],[170],753⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨753,[1,2,3,5,6,7,10,11,13,14,15],754⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2529 : RecordDataValid section14Catalog 13 (⟨225,(10),[1,2,5,6,13,14],[170],755⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨755,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],756⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2530 : RecordDataValid section14Catalog 13 (⟨225,(11),[1,2,5,6,13,14],[170],756⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨756,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],757⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2531 : RecordDataValid section14Catalog 13 (⟨225,(12),[1,2,5,6,13,14],[170],757⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨757,[1,2,3,5,6,7,10,11,13,14,15],758⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2532 : RecordDataValid section14Catalog 13 (⟨225,(13),[1,2,5,6,13,14],[170],758⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨758,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],759⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2533 : RecordDataValid section14Catalog 13 (⟨225,(14),[1,2,5,6,13,14],[170],757⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨757,[1,2,3,5,6,7,10,11,13,14,15],758⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2534 : RecordDataValid section14Catalog 13 (⟨225,(15),[1,2,5,6,13,14],[170],759⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨759,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],760⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2535 : RecordDataValid section14Catalog 13 (⟨225,(16),[1,2,5,6,13,14],[170],760⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨760,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],761⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2536 : RecordDataValid section14Catalog 13 (⟨225,(17),[1,2,5,6,13,14],[170],761⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨761,[1,2,3,5,6,7,10,11,13,14,15],762⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2537 : RecordDataValid section14Catalog 13 (⟨225,(18),[1,2,5,6,13,14],[170],762⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨762,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],763⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2538 : RecordDataValid section14Catalog 13 (⟨225,(19),[1,2,5,6,13,14],[170],761⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨761,[1,2,3,5,6,7,10,11,13,14,15],762⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2539 : RecordDataValid section14Catalog 13 (⟨225,(20),[1,2,5,6,13,14],[170],763⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨763,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],764⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2540 : RecordDataValid section14Catalog 13 (⟨225,(21),[1,2,5,6,13,14],[170],764⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨764,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],765⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2541 : RecordDataValid section14Catalog 13 (⟨225,(22),[1,2,5,6,13,14],[170],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2542 : RecordDataValid section14Catalog 13 (⟨225,(23),[1,2,5,6,13,14],[170],765⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨765,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],766⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2543 : RecordDataValid section14Catalog 13 (⟨225,(24),[1,2,5,6,13,14],[170],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2544 : RecordDataValid section14Catalog 13 (⟨226,(0),[1,2,5,6,13,14],[170],766⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨766,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],767⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2545 : RecordDataValid section14Catalog 13 (⟨226,(1),[1,2,5,6,13,14],[170],767⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨767,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],768⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2546 : RecordDataValid section14Catalog 13 (⟨226,(2),[1,2,5,6,13,14],[170],768⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨768,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],769⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2547 : RecordDataValid section14Catalog 13 (⟨226,(3),[1,2,5,6,13,14],[170],767⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨767,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],768⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2548 : RecordDataValid section14Catalog 13 (⟨226,(4),[1,2,5,6,13,14],[170],769⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨769,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],770⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2549 : RecordDataValid section14Catalog 13 (⟨226,(5),[1,2,5,6,13,14],[170],770⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨770,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],771⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2550 : RecordDataValid section14Catalog 13 (⟨226,(6),[1,2,5,6,13,14],[170],771⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨771,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],772⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2551 : RecordDataValid section14Catalog 13 (⟨226,(7),[1,2,5,6,13,14],[170],771⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨771,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],772⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2552 : RecordDataValid section14Catalog 13 (⟨226,(8),[1,2,5,6,13,14],[170],772⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨772,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],773⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2553 : RecordDataValid section14Catalog 13 (⟨226,(9),[1,2,5,6,13,14],[170],772⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨772,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],773⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2554 : RecordDataValid section14Catalog 13 (⟨227,(0),[1,2,5,6,13,14],[170],773⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨773,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],774⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2555 : RecordDataValid section14Catalog 13 (⟨227,(1),[1,2,5,6,13,14],[170],774⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨774,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],775⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2556 : RecordDataValid section14Catalog 13 (⟨227,(2),[1,2,5,6,13,14],[170],775⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨775,[1,2,3,5,6,7,10,11,13,14,15],776⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2557 : RecordDataValid section14Catalog 13 (⟨227,(3),[1,2,5,6,13,14],[170],776⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨776,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],777⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2558 : RecordDataValid section14Catalog 13 (⟨227,(4),[1,2,5,6,13,14],[170],775⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨775,[1,2,3,5,6,7,10,11,13,14,15],776⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2559 : RecordDataValid section14Catalog 13 (⟨227,(5),[1,2,5,6,13,14],[170],773⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨773,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],774⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_2528_2560 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2528).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2528).take 32 = [⟨225,(9),[1,2,5,6,13,14],[170],753⟩,⟨225,(10),[1,2,5,6,13,14],[170],755⟩,⟨225,(11),[1,2,5,6,13,14],[170],756⟩,⟨225,(12),[1,2,5,6,13,14],[170],757⟩,⟨225,(13),[1,2,5,6,13,14],[170],758⟩,⟨225,(14),[1,2,5,6,13,14],[170],757⟩,⟨225,(15),[1,2,5,6,13,14],[170],759⟩,⟨225,(16),[1,2,5,6,13,14],[170],760⟩,⟨225,(17),[1,2,5,6,13,14],[170],761⟩,⟨225,(18),[1,2,5,6,13,14],[170],762⟩,⟨225,(19),[1,2,5,6,13,14],[170],761⟩,⟨225,(20),[1,2,5,6,13,14],[170],763⟩,⟨225,(21),[1,2,5,6,13,14],[170],764⟩,⟨225,(22),[1,2,5,6,13,14],[170],547⟩,⟨225,(23),[1,2,5,6,13,14],[170],765⟩,⟨225,(24),[1,2,5,6,13,14],[170],547⟩,⟨226,(0),[1,2,5,6,13,14],[170],766⟩,⟨226,(1),[1,2,5,6,13,14],[170],767⟩,⟨226,(2),[1,2,5,6,13,14],[170],768⟩,⟨226,(3),[1,2,5,6,13,14],[170],767⟩,⟨226,(4),[1,2,5,6,13,14],[170],769⟩,⟨226,(5),[1,2,5,6,13,14],[170],770⟩,⟨226,(6),[1,2,5,6,13,14],[170],771⟩,⟨226,(7),[1,2,5,6,13,14],[170],771⟩,⟨226,(8),[1,2,5,6,13,14],[170],772⟩,⟨226,(9),[1,2,5,6,13,14],[170],772⟩,⟨227,(0),[1,2,5,6,13,14],[170],773⟩,⟨227,(1),[1,2,5,6,13,14],[170],774⟩,⟨227,(2),[1,2,5,6,13,14],[170],775⟩,⟨227,(3),[1,2,5,6,13,14],[170],776⟩,⟨227,(4),[1,2,5,6,13,14],[170],775⟩,⟨227,(5),[1,2,5,6,13,14],[170],773⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2528
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2529
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2530
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2531
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2532
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2533
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2534
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2535
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2536
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2537
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2538
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2539
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2540
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2541
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2542
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2543
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2544
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2545
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2546
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2547
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2548
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2549
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2550
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2551
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2552
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2553
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2554
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2555
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2556
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2557
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2558
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2559
end Section14Records_13_2528_2560

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2528_2560


namespace WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2560_2592
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_13_2560_2592
private theorem valid2560 : RecordDataValid section14Catalog 13 (⟨227,(6),[1,2,5,6,13,14],[170],774⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨774,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],775⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2561 : RecordDataValid section14Catalog 13 (⟨227,(7),[1,2,5,6,13,14],[170],775⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨775,[1,2,3,5,6,7,10,11,13,14,15],776⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2562 : RecordDataValid section14Catalog 13 (⟨227,(8),[1,2,5,6,13,14],[170],776⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨776,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],777⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2563 : RecordDataValid section14Catalog 13 (⟨227,(9),[1,2,5,6,13,14],[170],775⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨775,[1,2,3,5,6,7,10,11,13,14,15],776⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2564 : RecordDataValid section14Catalog 13 (⟨227,(10),[1,2,5,6,13,14],[170],777⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨777,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],778⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2565 : RecordDataValid section14Catalog 13 (⟨227,(11),[1,2,5,6,13,14],[170],778⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨778,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],779⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2566 : RecordDataValid section14Catalog 13 (⟨227,(12),[1,2,5,6,13,14],[170],779⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨779,[1,2,3,5,6,7,10,11,13,14,15],780⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2567 : RecordDataValid section14Catalog 13 (⟨227,(13),[1,2,5,6,13,14],[170],780⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨780,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],781⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2568 : RecordDataValid section14Catalog 13 (⟨227,(14),[1,2,5,6,13,14],[170],779⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨779,[1,2,3,5,6,7,10,11,13,14,15],780⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2569 : RecordDataValid section14Catalog 13 (⟨227,(15),[1,2,5,6,13,14],[170],781⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨781,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],782⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2570 : RecordDataValid section14Catalog 13 (⟨227,(16),[1,2,5,6,13,14],[170],782⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨782,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],783⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2571 : RecordDataValid section14Catalog 13 (⟨227,(17),[1,2,5,6,13,14],[170],783⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨783,[1,2,3,5,6,7,10,11,13,14,15],784⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2572 : RecordDataValid section14Catalog 13 (⟨227,(18),[1,2,5,6,13,14],[170],784⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨784,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],785⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2573 : RecordDataValid section14Catalog 13 (⟨227,(19),[1,2,5,6,13,14],[170],783⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨783,[1,2,3,5,6,7,10,11,13,14,15],784⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2574 : RecordDataValid section14Catalog 13 (⟨227,(20),[1,2,5,6,13,14],[170],785⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨785,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],786⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2575 : RecordDataValid section14Catalog 13 (⟨227,(21),[1,2,5,6,13,14],[170],786⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨786,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],787⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2576 : RecordDataValid section14Catalog 13 (⟨227,(22),[1,2,5,6,13,14],[170],787⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨787,[1,2,3,5,6,7,10,11,13,14,15],788⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2577 : RecordDataValid section14Catalog 13 (⟨227,(23),[1,2,5,6,13,14],[170],788⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨788,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],789⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2578 : RecordDataValid section14Catalog 13 (⟨227,(24),[1,2,5,6,13,14],[170],787⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨787,[1,2,3,5,6,7,10,11,13,14,15],788⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2579 : RecordDataValid section14Catalog 13 (⟨228,(0),[1,2,5,6,13,14],[170],789⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨789,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],790⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2580 : RecordDataValid section14Catalog 13 (⟨228,(1),[1,2,5,6,13,14],[170],790⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨790,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],791⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2581 : RecordDataValid section14Catalog 13 (⟨228,(2),[1,5,6,13],[170],791⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨791,[1,4,5,6,7,8,9,10,11,12,13,16],792⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2582 : RecordDataValid section14Catalog 13 (⟨228,(3),[1,2,5,6,13,14],[170],792⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨792,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],793⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2583 : RecordDataValid section14Catalog 13 (⟨228,(4),[1,2,5,6,13,14],[170],793⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨793,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],794⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2584 : RecordDataValid section14Catalog 13 (⟨228,(5),[1,2,5,6,13,14],[170],794⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨794,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],795⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2585 : RecordDataValid section14Catalog 13 (⟨228,(6),[1,2,5,6,13,14],[170],795⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨795,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],796⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2586 : RecordDataValid section14Catalog 13 (⟨228,(7),[1,2,5,6,13,14],[170],796⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨796,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],797⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2587 : RecordDataValid section14Catalog 13 (⟨228,(8),[1,2,5,6,13,14],[170],797⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨797,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],798⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2588 : RecordDataValid section14Catalog 13 (⟨228,(9),[1,2,5,6,13,14],[170],796⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨796,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],797⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2589 : RecordDataValid section14Catalog 13 (⟨228,(10),[1,2,5,6,13,14],[170],798⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨798,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],799⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2590 : RecordDataValid section14Catalog 13 (⟨228,(11),[1,2,5,6,13,14],[170],799⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨799,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],800⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2591 : RecordDataValid section14Catalog 13 (⟨228,(12),[1,2,5,6,13,14],[170],800⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨800,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],801⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0013_records_2560_2592 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2560).take 32, section14RecordValid section14Catalog 13 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2560).take 32 = [⟨227,(6),[1,2,5,6,13,14],[170],774⟩,⟨227,(7),[1,2,5,6,13,14],[170],775⟩,⟨227,(8),[1,2,5,6,13,14],[170],776⟩,⟨227,(9),[1,2,5,6,13,14],[170],775⟩,⟨227,(10),[1,2,5,6,13,14],[170],777⟩,⟨227,(11),[1,2,5,6,13,14],[170],778⟩,⟨227,(12),[1,2,5,6,13,14],[170],779⟩,⟨227,(13),[1,2,5,6,13,14],[170],780⟩,⟨227,(14),[1,2,5,6,13,14],[170],779⟩,⟨227,(15),[1,2,5,6,13,14],[170],781⟩,⟨227,(16),[1,2,5,6,13,14],[170],782⟩,⟨227,(17),[1,2,5,6,13,14],[170],783⟩,⟨227,(18),[1,2,5,6,13,14],[170],784⟩,⟨227,(19),[1,2,5,6,13,14],[170],783⟩,⟨227,(20),[1,2,5,6,13,14],[170],785⟩,⟨227,(21),[1,2,5,6,13,14],[170],786⟩,⟨227,(22),[1,2,5,6,13,14],[170],787⟩,⟨227,(23),[1,2,5,6,13,14],[170],788⟩,⟨227,(24),[1,2,5,6,13,14],[170],787⟩,⟨228,(0),[1,2,5,6,13,14],[170],789⟩,⟨228,(1),[1,2,5,6,13,14],[170],790⟩,⟨228,(2),[1,5,6,13],[170],791⟩,⟨228,(3),[1,2,5,6,13,14],[170],792⟩,⟨228,(4),[1,2,5,6,13,14],[170],793⟩,⟨228,(5),[1,2,5,6,13,14],[170],794⟩,⟨228,(6),[1,2,5,6,13,14],[170],795⟩,⟨228,(7),[1,2,5,6,13,14],[170],796⟩,⟨228,(8),[1,2,5,6,13,14],[170],797⟩,⟨228,(9),[1,2,5,6,13,14],[170],796⟩,⟨228,(10),[1,2,5,6,13,14],[170],798⟩,⟨228,(11),[1,2,5,6,13,14],[170],799⟩,⟨228,(12),[1,2,5,6,13,14],[170],800⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2560
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2561
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2562
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2563
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2564
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2565
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2566
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2567
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2568
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2569
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2570
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2571
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2572
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2573
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2574
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2575
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2576
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2577
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2578
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2579
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2580
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2581
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2582
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2583
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2584
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2585
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2586
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2587
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2588
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2589
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2590
  · exact recordValid_of_data section14Catalog 13 _ hnum valid2591
end Section14Records_13_2560_2592

end WorkReverseInterface_Freiman_workReverse20260919_s0013_records_2560_2592

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (13 ∈ r.states))).drop 2496).take 96, section14RecordValid section14Catalog 13 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (13 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 13 r
  exact (all_of_interval_split P xs 2496 2528 2592 (by decide) (by decide) (Freiman.workReverse20260919_s0013_records_2496_2528 hnum) (all_of_interval_split P xs 2528 2560 2592 (by decide) (by decide) (Freiman.workReverse20260919_s0013_records_2528_2560 hnum) (Freiman.workReverse20260919_s0013_records_2560_2592 hnum)))

#print axioms solution
