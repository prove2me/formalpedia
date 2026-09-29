-- Prove2me | solution 1 for Freiman.section14_s0016_records_0576_0608
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T22:54:36.507705+00:00
-- url     : https://prove2.me/submissions/d9a430ff-a03c-4c54-a1a6-acc295d4e0eb

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
namespace Section14Records_16_576_608
private theorem valid576 : RecordDataValid section14Catalog 16 (⟨114,(22),[4,8,12,16],[10],464⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨464,[1,4,5,6,8,9,10,12,13,16],465⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid577 : RecordDataValid section14Catalog 16 (⟨114,(23),[4,8,12,16],[10],463⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨463,[1,4,5,6,8,9,10,12,13,16],464⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid578 : RecordDataValid section14Catalog 16 (⟨114,(24),[4,8,12,16],[10],465⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨465,[1,4,5,6,8,9,10,12,13,16],466⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid579 : RecordDataValid section14Catalog 16 (⟨116,(0),[4,8,12,16],[10],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid580 : RecordDataValid section14Catalog 16 (⟨116,(1),[4,8,12,16],[10],468⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨468,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid581 : RecordDataValid section14Catalog 16 (⟨116,(2),[4,8,12,16],[10],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid582 : RecordDataValid section14Catalog 16 (⟨116,(3),[4,8,12,16],[10],469⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨469,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],470⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid583 : RecordDataValid section14Catalog 16 (⟨116,(4),[4,8,12,16],[10],470⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨470,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid584 : RecordDataValid section14Catalog 16 (⟨116,(5),[4,8,12,16],[10],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid585 : RecordDataValid section14Catalog 16 (⟨116,(6),[4,8,12,16],[10],468⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨468,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],469⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid586 : RecordDataValid section14Catalog 16 (⟨116,(7),[4,8,12,16],[10],467⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid587 : RecordDataValid section14Catalog 16 (⟨116,(8),[4,8,12,16],[10],469⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨469,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],470⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid588 : RecordDataValid section14Catalog 16 (⟨116,(9),[4,8,12,16],[10],470⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨470,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid589 : RecordDataValid section14Catalog 16 (⟨116,(10),[4,8,12,16],[10],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid590 : RecordDataValid section14Catalog 16 (⟨116,(11),[4,8,12,16],[10],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid591 : RecordDataValid section14Catalog 16 (⟨116,(12),[4,8,12,16],[10],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid592 : RecordDataValid section14Catalog 16 (⟨116,(13),[4,8,12,16],[10],471⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid593 : RecordDataValid section14Catalog 16 (⟨116,(14),[4,8,12,16],[10],470⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨470,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],471⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid594 : RecordDataValid section14Catalog 16 (⟨116,(15),[4,8,12,16],[10],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid595 : RecordDataValid section14Catalog 16 (⟨116,(16),[4,8,12,16],[10],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid596 : RecordDataValid section14Catalog 16 (⟨116,(17),[4,8,12,16],[10],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid597 : RecordDataValid section14Catalog 16 (⟨116,(18),[4,8,12,16],[10],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid598 : RecordDataValid section14Catalog 16 (⟨116,(19),[4,8,12,16],[10],472⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid599 : RecordDataValid section14Catalog 16 (⟨116,(20),[4,8,12,16],[10],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid600 : RecordDataValid section14Catalog 16 (⟨116,(21),[4,8,12,16],[10],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid601 : RecordDataValid section14Catalog 16 (⟨116,(22),[4,8,12,16],[10],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid602 : RecordDataValid section14Catalog 16 (⟨116,(23),[4,8,12,16],[10],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid603 : RecordDataValid section14Catalog 16 (⟨116,(24),[4,8,12,16],[10],473⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid604 : RecordDataValid section14Catalog 16 (⟨119,(0),[4,8,12,16],[10],474⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨474,[1,4,5,6,8,9,10,12,13,16],475⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid605 : RecordDataValid section14Catalog 16 (⟨119,(1),[4,8,12,16],[10],474⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨474,[1,4,5,6,8,9,10,12,13,16],475⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid606 : RecordDataValid section14Catalog 16 (⟨119,(2),[4,8,12,16],[10],474⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨474,[1,4,5,6,8,9,10,12,13,16],475⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid607 : RecordDataValid section14Catalog 16 (⟨119,(3),[4,8,12,16],[10],712⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨712,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],713⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 576).take 32, section14RecordValid section14Catalog 16 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (16 ∈ r.states))).drop 576).take 32 = [⟨114,(22),[4,8,12,16],[10],464⟩,⟨114,(23),[4,8,12,16],[10],463⟩,⟨114,(24),[4,8,12,16],[10],465⟩,⟨116,(0),[4,8,12,16],[10],467⟩,⟨116,(1),[4,8,12,16],[10],468⟩,⟨116,(2),[4,8,12,16],[10],467⟩,⟨116,(3),[4,8,12,16],[10],469⟩,⟨116,(4),[4,8,12,16],[10],470⟩,⟨116,(5),[4,8,12,16],[10],467⟩,⟨116,(6),[4,8,12,16],[10],468⟩,⟨116,(7),[4,8,12,16],[10],467⟩,⟨116,(8),[4,8,12,16],[10],469⟩,⟨116,(9),[4,8,12,16],[10],470⟩,⟨116,(10),[4,8,12,16],[10],471⟩,⟨116,(11),[4,8,12,16],[10],471⟩,⟨116,(12),[4,8,12,16],[10],471⟩,⟨116,(13),[4,8,12,16],[10],471⟩,⟨116,(14),[4,8,12,16],[10],470⟩,⟨116,(15),[4,8,12,16],[10],472⟩,⟨116,(16),[4,8,12,16],[10],472⟩,⟨116,(17),[4,8,12,16],[10],472⟩,⟨116,(18),[4,8,12,16],[10],472⟩,⟨116,(19),[4,8,12,16],[10],472⟩,⟨116,(20),[4,8,12,16],[10],473⟩,⟨116,(21),[4,8,12,16],[10],473⟩,⟨116,(22),[4,8,12,16],[10],473⟩,⟨116,(23),[4,8,12,16],[10],473⟩,⟨116,(24),[4,8,12,16],[10],473⟩,⟨119,(0),[4,8,12,16],[10],474⟩,⟨119,(1),[4,8,12,16],[10],474⟩,⟨119,(2),[4,8,12,16],[10],474⟩,⟨119,(3),[4,8,12,16],[10],712⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 16 _ hnum valid576
  · exact recordValid_of_data section14Catalog 16 _ hnum valid577
  · exact recordValid_of_data section14Catalog 16 _ hnum valid578
  · exact recordValid_of_data section14Catalog 16 _ hnum valid579
  · exact recordValid_of_data section14Catalog 16 _ hnum valid580
  · exact recordValid_of_data section14Catalog 16 _ hnum valid581
  · exact recordValid_of_data section14Catalog 16 _ hnum valid582
  · exact recordValid_of_data section14Catalog 16 _ hnum valid583
  · exact recordValid_of_data section14Catalog 16 _ hnum valid584
  · exact recordValid_of_data section14Catalog 16 _ hnum valid585
  · exact recordValid_of_data section14Catalog 16 _ hnum valid586
  · exact recordValid_of_data section14Catalog 16 _ hnum valid587
  · exact recordValid_of_data section14Catalog 16 _ hnum valid588
  · exact recordValid_of_data section14Catalog 16 _ hnum valid589
  · exact recordValid_of_data section14Catalog 16 _ hnum valid590
  · exact recordValid_of_data section14Catalog 16 _ hnum valid591
  · exact recordValid_of_data section14Catalog 16 _ hnum valid592
  · exact recordValid_of_data section14Catalog 16 _ hnum valid593
  · exact recordValid_of_data section14Catalog 16 _ hnum valid594
  · exact recordValid_of_data section14Catalog 16 _ hnum valid595
  · exact recordValid_of_data section14Catalog 16 _ hnum valid596
  · exact recordValid_of_data section14Catalog 16 _ hnum valid597
  · exact recordValid_of_data section14Catalog 16 _ hnum valid598
  · exact recordValid_of_data section14Catalog 16 _ hnum valid599
  · exact recordValid_of_data section14Catalog 16 _ hnum valid600
  · exact recordValid_of_data section14Catalog 16 _ hnum valid601
  · exact recordValid_of_data section14Catalog 16 _ hnum valid602
  · exact recordValid_of_data section14Catalog 16 _ hnum valid603
  · exact recordValid_of_data section14Catalog 16 _ hnum valid604
  · exact recordValid_of_data section14Catalog 16 _ hnum valid605
  · exact recordValid_of_data section14Catalog 16 _ hnum valid606
  · exact recordValid_of_data section14Catalog 16 _ hnum valid607
end Section14Records_16_576_608

#print axioms solution
