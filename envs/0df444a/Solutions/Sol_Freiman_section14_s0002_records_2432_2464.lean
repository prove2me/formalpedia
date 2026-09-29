-- Prove2me | solution 1 for Freiman.section14_s0002_records_2432_2464
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:06:46.545647+00:00
-- url     : https://prove2.me/submissions/96b0bb85-4b98-40b4-ad40-50a643fc486a

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
namespace Section14Records_2_2432_2464
private theorem valid2432 : RecordDataValid section14Catalog 2 (⟨235,(10),[1,2,5,6,13,14],[170],580⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨580,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],581⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2433 : RecordDataValid section14Catalog 2 (⟨235,(11),[1,2,5,6,13,14],[170],581⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨581,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],582⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2434 : RecordDataValid section14Catalog 2 (⟨235,(12),[1,2,5,6,13,14],[170],586⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨586,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],587⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2435 : RecordDataValid section14Catalog 2 (⟨235,(13),[1,2,5,6,13,14],[170],587⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨587,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],588⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2436 : RecordDataValid section14Catalog 2 (⟨235,(14),[1,2,5,6,13,14],[170],588⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨588,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],589⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2437 : RecordDataValid section14Catalog 2 (⟨235,(15),[1,2,5,6,13,14],[170],589⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨589,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],590⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2438 : RecordDataValid section14Catalog 2 (⟨236,(0),[1,2,5,6,13,14],[170],861⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨861,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],862⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2439 : RecordDataValid section14Catalog 2 (⟨236,(1),[1,2,5,6,13,14],[170],862⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨862,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],863⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2440 : RecordDataValid section14Catalog 2 (⟨236,(2),[1,2,6,13,14],[170],863⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨863,[1,2,3,6,7,10,11,13,14,15],864⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2441 : RecordDataValid section14Catalog 2 (⟨236,(3),[1,2,5,6,13,14],[170],864⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨864,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],865⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2442 : RecordDataValid section14Catalog 2 (⟨237,(0),[1,2,5,6,13,14],[170],865⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨865,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],866⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2443 : RecordDataValid section14Catalog 2 (⟨237,(1),[1,2,5,6,13,14],[170],594⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨594,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],595⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2444 : RecordDataValid section14Catalog 2 (⟨237,(2),[1,2,5,6,13,14],[170],595⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨595,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],596⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2445 : RecordDataValid section14Catalog 2 (⟨237,(3),[1,2,5,6,13,14],[170],596⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨596,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],597⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2446 : RecordDataValid section14Catalog 2 (⟨237,(4),[1,2,5,6,13,14],[170],866⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨866,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],867⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2447 : RecordDataValid section14Catalog 2 (⟨237,(5),[1,2,5,6,13,14],[170],598⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨598,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],599⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2448 : RecordDataValid section14Catalog 2 (⟨237,(6),[1,2,5,6,13,14],[170],599⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨599,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],600⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2449 : RecordDataValid section14Catalog 2 (⟨237,(7),[1,2,5,6,13,14],[170],600⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨600,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],601⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2450 : RecordDataValid section14Catalog 2 (⟨237,(8),[1,2,6,13,14],[170],867⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨867,[1,2,3,6,7,10,11,13,14,15],868⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2451 : RecordDataValid section14Catalog 2 (⟨237,(9),[1,2,5,6,13,14],[170],594⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨594,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],595⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2452 : RecordDataValid section14Catalog 2 (⟨237,(10),[1,2,5,6,13,14],[170],595⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨595,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],596⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2453 : RecordDataValid section14Catalog 2 (⟨237,(11),[1,2,5,6,13,14],[170],596⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨596,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],597⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2454 : RecordDataValid section14Catalog 2 (⟨237,(12),[1,2,5,6,13,14],[170],868⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨868,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],869⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2455 : RecordDataValid section14Catalog 2 (⟨237,(13),[1,2,5,6,13,14],[170],602⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨602,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],603⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2456 : RecordDataValid section14Catalog 2 (⟨237,(14),[1,2,5,6,13,14],[170],603⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨603,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],604⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2457 : RecordDataValid section14Catalog 2 (⟨237,(15),[1,2,5,6,13,14],[170],604⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨604,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],605⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2458 : RecordDataValid section14Catalog 2 (⟨238,(0),[1,2,5,6,13,14],[170],869⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨869,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],870⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2459 : RecordDataValid section14Catalog 2 (⟨238,(1),[1,2,5,6,13,14],[170],870⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨870,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],871⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2460 : RecordDataValid section14Catalog 2 (⟨238,(2),[1,2,5,6,13,14],[170],607⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨607,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],608⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2461 : RecordDataValid section14Catalog 2 (⟨238,(3),[1,2,5,6,13,14],[170],871⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨871,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],872⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2462 : RecordDataValid section14Catalog 2 (⟨238,(4),[1,2,5,6,13,14],[170],609⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨609,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],610⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid2463 : RecordDataValid section14Catalog 2 (⟨238,(5),[1,2,5,6,13,14],[170],610⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨610,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],611⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 2432).take 32, section14RecordValid section14Catalog 2 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (2 ∈ r.states))).drop 2432).take 32 = [⟨235,(10),[1,2,5,6,13,14],[170],580⟩,⟨235,(11),[1,2,5,6,13,14],[170],581⟩,⟨235,(12),[1,2,5,6,13,14],[170],586⟩,⟨235,(13),[1,2,5,6,13,14],[170],587⟩,⟨235,(14),[1,2,5,6,13,14],[170],588⟩,⟨235,(15),[1,2,5,6,13,14],[170],589⟩,⟨236,(0),[1,2,5,6,13,14],[170],861⟩,⟨236,(1),[1,2,5,6,13,14],[170],862⟩,⟨236,(2),[1,2,6,13,14],[170],863⟩,⟨236,(3),[1,2,5,6,13,14],[170],864⟩,⟨237,(0),[1,2,5,6,13,14],[170],865⟩,⟨237,(1),[1,2,5,6,13,14],[170],594⟩,⟨237,(2),[1,2,5,6,13,14],[170],595⟩,⟨237,(3),[1,2,5,6,13,14],[170],596⟩,⟨237,(4),[1,2,5,6,13,14],[170],866⟩,⟨237,(5),[1,2,5,6,13,14],[170],598⟩,⟨237,(6),[1,2,5,6,13,14],[170],599⟩,⟨237,(7),[1,2,5,6,13,14],[170],600⟩,⟨237,(8),[1,2,6,13,14],[170],867⟩,⟨237,(9),[1,2,5,6,13,14],[170],594⟩,⟨237,(10),[1,2,5,6,13,14],[170],595⟩,⟨237,(11),[1,2,5,6,13,14],[170],596⟩,⟨237,(12),[1,2,5,6,13,14],[170],868⟩,⟨237,(13),[1,2,5,6,13,14],[170],602⟩,⟨237,(14),[1,2,5,6,13,14],[170],603⟩,⟨237,(15),[1,2,5,6,13,14],[170],604⟩,⟨238,(0),[1,2,5,6,13,14],[170],869⟩,⟨238,(1),[1,2,5,6,13,14],[170],870⟩,⟨238,(2),[1,2,5,6,13,14],[170],607⟩,⟨238,(3),[1,2,5,6,13,14],[170],871⟩,⟨238,(4),[1,2,5,6,13,14],[170],609⟩,⟨238,(5),[1,2,5,6,13,14],[170],610⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2432
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2433
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2434
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2435
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2436
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2437
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2438
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2439
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2440
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2441
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2442
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2443
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2444
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2445
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2446
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2447
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2448
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2449
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2450
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2451
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2452
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2453
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2454
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2455
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2456
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2457
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2458
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2459
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2460
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2461
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2462
  · exact recordValid_of_data section14Catalog 2 _ hnum valid2463
end Section14Records_2_2432_2464

#print axioms solution
