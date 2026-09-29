-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_3328_3392
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T08:30:35.288391+00:00
-- url     : https://prove2.me/submissions/a6e774a2-b1fc-467f-aa8a-78e25208dea9

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3328_3360
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_3328_3360
private theorem valid3328 : RecordDataValid section14Catalog 6 (⟨224,(21),[5,6],[174],1048⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1048,[3,5,6,7],1052⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3329 : RecordDataValid section14Catalog 6 (⟨224,(22),[1,2,5,6,13,14],[170],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3330 : RecordDataValid section14Catalog 6 (⟨224,(22),[5,6],[174],1048⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1048,[3,5,6,7],1052⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3331 : RecordDataValid section14Catalog 6 (⟨224,(23),[1,2,5,6,13,14],[170],517⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨517,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],518⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3332 : RecordDataValid section14Catalog 6 (⟨224,(23),[5,6],[174],1038⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1038,[3,5,6,7],1042⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3333 : RecordDataValid section14Catalog 6 (⟨224,(24),[1,2,5,6,13,14],[170],518⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨518,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],519⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3334 : RecordDataValid section14Catalog 6 (⟨224,(24),[5,6],[174],1039⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1039,[3,5,6,7],1043⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3335 : RecordDataValid section14Catalog 6 (⟨225,(0),[1,2,5,6,13,14],[170],747⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨747,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],748⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3336 : RecordDataValid section14Catalog 6 (⟨225,(0),[5,6],[174],747⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨747,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],748⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3337 : RecordDataValid section14Catalog 6 (⟨225,(1),[1,2,5,6,13,14],[170],748⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨748,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],749⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3338 : RecordDataValid section14Catalog 6 (⟨225,(1),[5,6],[174],748⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨748,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],749⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3339 : RecordDataValid section14Catalog 6 (⟨225,(2),[1,2,5,6,13,14],[170],749⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨749,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],750⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3340 : RecordDataValid section14Catalog 6 (⟨225,(2),[5,6],[174],749⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨749,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],750⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3341 : RecordDataValid section14Catalog 6 (⟨225,(3),[1,2,5,6,13,14],[170],750⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨750,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],751⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3342 : RecordDataValid section14Catalog 6 (⟨225,(3),[5,6],[174],750⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨750,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],751⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3343 : RecordDataValid section14Catalog 6 (⟨225,(4),[1,2,5,6,13,14],[170],749⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨749,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],750⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3344 : RecordDataValid section14Catalog 6 (⟨225,(4),[5,6],[174],749⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨749,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],750⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3345 : RecordDataValid section14Catalog 6 (⟨225,(5),[1,2,5,6,13,14],[170],751⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨751,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],752⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3346 : RecordDataValid section14Catalog 6 (⟨225,(5),[5,6],[174],751⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨751,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],752⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3347 : RecordDataValid section14Catalog 6 (⟨225,(6),[1,2,5,6,13,14],[170],752⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨752,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],753⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3348 : RecordDataValid section14Catalog 6 (⟨225,(6),[5,6],[174],752⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨752,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],753⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3349 : RecordDataValid section14Catalog 6 (⟨225,(7),[1,2,5,6,13,14],[170],753⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨753,[1,2,3,5,6,7,10,11,13,14,15],754⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3350 : RecordDataValid section14Catalog 6 (⟨225,(7),[5,6],[174],1051⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1051,[3,5,6,7],1055⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3351 : RecordDataValid section14Catalog 6 (⟨225,(8),[1,2,5,6,13,14],[170],754⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨754,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],755⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3352 : RecordDataValid section14Catalog 6 (⟨225,(8),[5,6],[174],754⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨754,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],755⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3353 : RecordDataValid section14Catalog 6 (⟨225,(9),[1,2,5,6,13,14],[170],753⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨753,[1,2,3,5,6,7,10,11,13,14,15],754⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3354 : RecordDataValid section14Catalog 6 (⟨225,(9),[5,6],[174],1051⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1051,[3,5,6,7],1055⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3355 : RecordDataValid section14Catalog 6 (⟨225,(10),[1,2,5,6,13,14],[170],755⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨755,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],756⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3356 : RecordDataValid section14Catalog 6 (⟨225,(10),[5,6],[174],755⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨755,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],756⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3357 : RecordDataValid section14Catalog 6 (⟨225,(11),[1,2,5,6,13,14],[170],756⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨756,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],757⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3358 : RecordDataValid section14Catalog 6 (⟨225,(11),[5,6],[174],756⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨756,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],757⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3359 : RecordDataValid section14Catalog 6 (⟨225,(12),[1,2,5,6,13,14],[170],757⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨757,[1,2,3,5,6,7,10,11,13,14,15],758⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_3328_3360 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3328).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3328).take 32 = [⟨224,(21),[5,6],[174],1048⟩,⟨224,(22),[1,2,5,6,13,14],[170],547⟩,⟨224,(22),[5,6],[174],1048⟩,⟨224,(23),[1,2,5,6,13,14],[170],517⟩,⟨224,(23),[5,6],[174],1038⟩,⟨224,(24),[1,2,5,6,13,14],[170],518⟩,⟨224,(24),[5,6],[174],1039⟩,⟨225,(0),[1,2,5,6,13,14],[170],747⟩,⟨225,(0),[5,6],[174],747⟩,⟨225,(1),[1,2,5,6,13,14],[170],748⟩,⟨225,(1),[5,6],[174],748⟩,⟨225,(2),[1,2,5,6,13,14],[170],749⟩,⟨225,(2),[5,6],[174],749⟩,⟨225,(3),[1,2,5,6,13,14],[170],750⟩,⟨225,(3),[5,6],[174],750⟩,⟨225,(4),[1,2,5,6,13,14],[170],749⟩,⟨225,(4),[5,6],[174],749⟩,⟨225,(5),[1,2,5,6,13,14],[170],751⟩,⟨225,(5),[5,6],[174],751⟩,⟨225,(6),[1,2,5,6,13,14],[170],752⟩,⟨225,(6),[5,6],[174],752⟩,⟨225,(7),[1,2,5,6,13,14],[170],753⟩,⟨225,(7),[5,6],[174],1051⟩,⟨225,(8),[1,2,5,6,13,14],[170],754⟩,⟨225,(8),[5,6],[174],754⟩,⟨225,(9),[1,2,5,6,13,14],[170],753⟩,⟨225,(9),[5,6],[174],1051⟩,⟨225,(10),[1,2,5,6,13,14],[170],755⟩,⟨225,(10),[5,6],[174],755⟩,⟨225,(11),[1,2,5,6,13,14],[170],756⟩,⟨225,(11),[5,6],[174],756⟩,⟨225,(12),[1,2,5,6,13,14],[170],757⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3328
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3329
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3330
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3331
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3332
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3333
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3334
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3335
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3336
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3337
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3338
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3339
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3340
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3341
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3342
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3343
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3344
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3345
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3346
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3347
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3348
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3349
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3350
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3351
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3352
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3353
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3354
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3355
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3356
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3357
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3358
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3359
end Section14Records_6_3328_3360

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3328_3360


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3360_3392
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_3360_3392
private theorem valid3360 : RecordDataValid section14Catalog 6 (⟨225,(12),[5,6],[174],1053⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1053,[3,5,6,7],1057⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3361 : RecordDataValid section14Catalog 6 (⟨225,(13),[1,2,5,6,13,14],[170],758⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨758,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],759⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3362 : RecordDataValid section14Catalog 6 (⟨225,(13),[5,6],[174],758⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨758,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],759⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3363 : RecordDataValid section14Catalog 6 (⟨225,(14),[1,2,5,6,13,14],[170],757⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨757,[1,2,3,5,6,7,10,11,13,14,15],758⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3364 : RecordDataValid section14Catalog 6 (⟨225,(14),[5,6],[174],1053⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1053,[3,5,6,7],1057⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3365 : RecordDataValid section14Catalog 6 (⟨225,(15),[1,2,5,6,13,14],[170],759⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨759,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],760⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3366 : RecordDataValid section14Catalog 6 (⟨225,(15),[5,6],[174],759⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨759,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],760⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3367 : RecordDataValid section14Catalog 6 (⟨225,(16),[1,2,5,6,13,14],[170],760⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨760,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],761⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3368 : RecordDataValid section14Catalog 6 (⟨225,(16),[5,6],[174],760⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨760,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],761⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3369 : RecordDataValid section14Catalog 6 (⟨225,(17),[1,2,5,6,13,14],[170],761⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨761,[1,2,3,5,6,7,10,11,13,14,15],762⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3370 : RecordDataValid section14Catalog 6 (⟨225,(17),[5,6],[174],1054⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1054,[3,5,6,7],1058⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3371 : RecordDataValid section14Catalog 6 (⟨225,(18),[1,2,5,6,13,14],[170],762⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨762,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],763⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3372 : RecordDataValid section14Catalog 6 (⟨225,(18),[5,6],[174],762⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨762,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],763⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3373 : RecordDataValid section14Catalog 6 (⟨225,(19),[1,2,5,6,13,14],[170],761⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨761,[1,2,3,5,6,7,10,11,13,14,15],762⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3374 : RecordDataValid section14Catalog 6 (⟨225,(19),[5,6],[174],1054⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1054,[3,5,6,7],1058⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3375 : RecordDataValid section14Catalog 6 (⟨225,(20),[1,2,5,6,13,14],[170],763⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨763,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],764⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3376 : RecordDataValid section14Catalog 6 (⟨225,(20),[5,6],[174],763⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨763,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],764⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3377 : RecordDataValid section14Catalog 6 (⟨225,(21),[1,2,5,6,13,14],[170],764⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨764,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],765⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3378 : RecordDataValid section14Catalog 6 (⟨225,(21),[5,6],[174],764⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨764,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],765⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3379 : RecordDataValid section14Catalog 6 (⟨225,(22),[1,2,5,6,13,14],[170],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3380 : RecordDataValid section14Catalog 6 (⟨225,(22),[5,6],[174],1048⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1048,[3,5,6,7],1052⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3381 : RecordDataValid section14Catalog 6 (⟨225,(23),[1,2,5,6,13,14],[170],765⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨765,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],766⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3382 : RecordDataValid section14Catalog 6 (⟨225,(23),[5,6],[174],765⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨765,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],766⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3383 : RecordDataValid section14Catalog 6 (⟨225,(24),[1,2,5,6,13,14],[170],547⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨547,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],548⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3384 : RecordDataValid section14Catalog 6 (⟨225,(24),[5,6],[174],1048⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1048,[3,5,6,7],1052⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3385 : RecordDataValid section14Catalog 6 (⟨226,(0),[1,2,5,6,13,14],[170],766⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨766,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],767⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3386 : RecordDataValid section14Catalog 6 (⟨226,(0),[5,6],[174],766⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨766,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],767⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3387 : RecordDataValid section14Catalog 6 (⟨226,(1),[1,2,5,6,13,14],[170],767⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨767,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],768⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3388 : RecordDataValid section14Catalog 6 (⟨226,(1),[5,6],[174],767⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨767,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],768⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3389 : RecordDataValid section14Catalog 6 (⟨226,(2),[1,2,5,6,13,14],[170],768⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨768,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],769⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3390 : RecordDataValid section14Catalog 6 (⟨226,(2),[5,6],[174],768⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨768,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],769⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid3391 : RecordDataValid section14Catalog 6 (⟨226,(3),[1,2,5,6,13,14],[170],767⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨767,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],768⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_3360_3392 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3360).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3360).take 32 = [⟨225,(12),[5,6],[174],1053⟩,⟨225,(13),[1,2,5,6,13,14],[170],758⟩,⟨225,(13),[5,6],[174],758⟩,⟨225,(14),[1,2,5,6,13,14],[170],757⟩,⟨225,(14),[5,6],[174],1053⟩,⟨225,(15),[1,2,5,6,13,14],[170],759⟩,⟨225,(15),[5,6],[174],759⟩,⟨225,(16),[1,2,5,6,13,14],[170],760⟩,⟨225,(16),[5,6],[174],760⟩,⟨225,(17),[1,2,5,6,13,14],[170],761⟩,⟨225,(17),[5,6],[174],1054⟩,⟨225,(18),[1,2,5,6,13,14],[170],762⟩,⟨225,(18),[5,6],[174],762⟩,⟨225,(19),[1,2,5,6,13,14],[170],761⟩,⟨225,(19),[5,6],[174],1054⟩,⟨225,(20),[1,2,5,6,13,14],[170],763⟩,⟨225,(20),[5,6],[174],763⟩,⟨225,(21),[1,2,5,6,13,14],[170],764⟩,⟨225,(21),[5,6],[174],764⟩,⟨225,(22),[1,2,5,6,13,14],[170],547⟩,⟨225,(22),[5,6],[174],1048⟩,⟨225,(23),[1,2,5,6,13,14],[170],765⟩,⟨225,(23),[5,6],[174],765⟩,⟨225,(24),[1,2,5,6,13,14],[170],547⟩,⟨225,(24),[5,6],[174],1048⟩,⟨226,(0),[1,2,5,6,13,14],[170],766⟩,⟨226,(0),[5,6],[174],766⟩,⟨226,(1),[1,2,5,6,13,14],[170],767⟩,⟨226,(1),[5,6],[174],767⟩,⟨226,(2),[1,2,5,6,13,14],[170],768⟩,⟨226,(2),[5,6],[174],768⟩,⟨226,(3),[1,2,5,6,13,14],[170],767⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3360
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3361
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3362
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3363
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3364
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3365
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3366
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3367
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3368
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3369
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3370
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3371
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3372
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3373
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3374
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3375
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3376
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3377
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3378
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3379
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3380
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3381
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3382
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3383
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3384
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3385
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3386
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3387
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3388
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3389
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3390
  · exact recordValid_of_data section14Catalog 6 _ hnum valid3391
end Section14Records_6_3360_3392

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_3360_3392

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 3328).take 64, section14RecordValid section14Catalog 6 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (6 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 6 r
  exact (all_of_interval_split P xs 3328 3360 3392 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_3328_3360 hnum) (Freiman.workReverse20260919_s0006_records_3360_3392 hnum))

#print axioms solution
