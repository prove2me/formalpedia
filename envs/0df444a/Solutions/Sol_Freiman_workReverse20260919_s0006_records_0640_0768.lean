-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_records_0640_0768
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-20T07:47:48.623011+00:00
-- url     : https://prove2.me/submissions/a347d0e5-bec7-41aa-9172-e20b41421891

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0640_0672
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_640_672
private theorem valid640 : RecordDataValid section14Catalog 6 (⟨33,(5),[1,2,5,6,13,14],[146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid641 : RecordDataValid section14Catalog 6 (⟨33,(5),[1,5,6],[130,131],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid642 : RecordDataValid section14Catalog 6 (⟨33,(6),[1,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid643 : RecordDataValid section14Catalog 6 (⟨33,(6),[1,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid644 : RecordDataValid section14Catalog 6 (⟨33,(7),[1,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid645 : RecordDataValid section14Catalog 6 (⟨33,(7),[1,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid646 : RecordDataValid section14Catalog 6 (⟨33,(8),[1,2,5,6],[130],97⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨97,[1,2,5,6,9,10,13,14],97⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid647 : RecordDataValid section14Catalog 6 (⟨33,(8),[1,2,5,6,13,14],[131],97⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨97,[1,2,5,6,9,10,13,14],97⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid648 : RecordDataValid section14Catalog 6 (⟨33,(8),[1,2,5,6,13,14],[146,150],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid649 : RecordDataValid section14Catalog 6 (⟨33,(9),[1,2,5,6],[130],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid650 : RecordDataValid section14Catalog 6 (⟨33,(9),[1,2,5,6,13,14],[131],98⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid651 : RecordDataValid section14Catalog 6 (⟨33,(9),[1,2,5,6,13,14],[146,150],159⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨159,[1,2,3,5,6,7,9,10,11,13,14,15],159⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid652 : RecordDataValid section14Catalog 6 (⟨33,(10),[1,2,5,6,13,14],[146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid653 : RecordDataValid section14Catalog 6 (⟨33,(10),[5,6],[130],97⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨97,[1,2,5,6,9,10,13,14],97⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid654 : RecordDataValid section14Catalog 6 (⟨33,(10),[5,6,13,14],[131],97⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨97,[1,2,5,6,9,10,13,14],97⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid655 : RecordDataValid section14Catalog 6 (⟨33,(11),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid656 : RecordDataValid section14Catalog 6 (⟨33,(11),[1,2,5,6,13,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid657 : RecordDataValid section14Catalog 6 (⟨33,(12),[1,2,5,6],[130,146,150],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid658 : RecordDataValid section14Catalog 6 (⟨33,(12),[1,2,5,6,13,14],[131],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid659 : RecordDataValid section14Catalog 6 (⟨33,(13),[1,2,5,6],[130,131],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid660 : RecordDataValid section14Catalog 6 (⟨33,(13),[1,2,5,6,13,14],[146,150],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid661 : RecordDataValid section14Catalog 6 (⟨33,(14),[6],[130],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid662 : RecordDataValid section14Catalog 6 (⟨33,(14),[6,13],[131,146,150],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid663 : RecordDataValid section14Catalog 6 (⟨33,(15),[6],[130],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid664 : RecordDataValid section14Catalog 6 (⟨33,(15),[6,13],[131,146,150],99⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid665 : RecordDataValid section14Catalog 6 (⟨35,(0),[1,2,5,6],[130,131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid666 : RecordDataValid section14Catalog 6 (⟨35,(1),[1,2,5,6],[130,131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid667 : RecordDataValid section14Catalog 6 (⟨35,(2),[1,2,5,6],[131],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid668 : RecordDataValid section14Catalog 6 (⟨35,(2),[1,2,5,6],[150],139⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨139,[1,2,3,5,6,7],139⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid669 : RecordDataValid section14Catalog 6 (⟨35,(2),[2,6],[130],121⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨121,[1,2,3,5,6,7,9,10,11],121⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid670 : RecordDataValid section14Catalog 6 (⟨35,(2),[6],[146],1527⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1527,[6],1532⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid671 : RecordDataValid section14Catalog 6 (⟨35,(3),[1,2,5,6],[130,146,150],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_0640_0672 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 640).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 640).take 32 = [⟨33,(5),[1,2,5,6,13,14],[146,150],2⟩,⟨33,(5),[1,5,6],[130,131],98⟩,⟨33,(6),[1,5,6],[130],3⟩,⟨33,(6),[1,5,6,13,14],[131,146,150],3⟩,⟨33,(7),[1,5,6],[130],3⟩,⟨33,(7),[1,5,6,13,14],[131,146,150],3⟩,⟨33,(8),[1,2,5,6],[130],97⟩,⟨33,(8),[1,2,5,6,13,14],[131],97⟩,⟨33,(8),[1,2,5,6,13,14],[146,150],98⟩,⟨33,(9),[1,2,5,6],[130],98⟩,⟨33,(9),[1,2,5,6,13,14],[131],98⟩,⟨33,(9),[1,2,5,6,13,14],[146,150],159⟩,⟨33,(10),[1,2,5,6,13,14],[146,150],3⟩,⟨33,(10),[5,6],[130],97⟩,⟨33,(10),[5,6,13,14],[131],97⟩,⟨33,(11),[1,2,5,6],[130],3⟩,⟨33,(11),[1,2,5,6,13,14],[131,146,150],3⟩,⟨33,(12),[1,2,5,6],[130,146,150],99⟩,⟨33,(12),[1,2,5,6,13,14],[131],99⟩,⟨33,(13),[1,2,5,6],[130,131],99⟩,⟨33,(13),[1,2,5,6,13,14],[146,150],99⟩,⟨33,(14),[6],[130],99⟩,⟨33,(14),[6,13],[131,146,150],99⟩,⟨33,(15),[6],[130],99⟩,⟨33,(15),[6,13],[131,146,150],99⟩,⟨35,(0),[1,2,5,6],[130,131,146,150],2⟩,⟨35,(1),[1,2,5,6],[130,131,146,150],2⟩,⟨35,(2),[1,2,5,6],[131],101⟩,⟨35,(2),[1,2,5,6],[150],139⟩,⟨35,(2),[2,6],[130],121⟩,⟨35,(2),[6],[146],1527⟩,⟨35,(3),[1,2,5,6],[130,146,150],101⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid640
  · exact recordValid_of_data section14Catalog 6 _ hnum valid641
  · exact recordValid_of_data section14Catalog 6 _ hnum valid642
  · exact recordValid_of_data section14Catalog 6 _ hnum valid643
  · exact recordValid_of_data section14Catalog 6 _ hnum valid644
  · exact recordValid_of_data section14Catalog 6 _ hnum valid645
  · exact recordValid_of_data section14Catalog 6 _ hnum valid646
  · exact recordValid_of_data section14Catalog 6 _ hnum valid647
  · exact recordValid_of_data section14Catalog 6 _ hnum valid648
  · exact recordValid_of_data section14Catalog 6 _ hnum valid649
  · exact recordValid_of_data section14Catalog 6 _ hnum valid650
  · exact recordValid_of_data section14Catalog 6 _ hnum valid651
  · exact recordValid_of_data section14Catalog 6 _ hnum valid652
  · exact recordValid_of_data section14Catalog 6 _ hnum valid653
  · exact recordValid_of_data section14Catalog 6 _ hnum valid654
  · exact recordValid_of_data section14Catalog 6 _ hnum valid655
  · exact recordValid_of_data section14Catalog 6 _ hnum valid656
  · exact recordValid_of_data section14Catalog 6 _ hnum valid657
  · exact recordValid_of_data section14Catalog 6 _ hnum valid658
  · exact recordValid_of_data section14Catalog 6 _ hnum valid659
  · exact recordValid_of_data section14Catalog 6 _ hnum valid660
  · exact recordValid_of_data section14Catalog 6 _ hnum valid661
  · exact recordValid_of_data section14Catalog 6 _ hnum valid662
  · exact recordValid_of_data section14Catalog 6 _ hnum valid663
  · exact recordValid_of_data section14Catalog 6 _ hnum valid664
  · exact recordValid_of_data section14Catalog 6 _ hnum valid665
  · exact recordValid_of_data section14Catalog 6 _ hnum valid666
  · exact recordValid_of_data section14Catalog 6 _ hnum valid667
  · exact recordValid_of_data section14Catalog 6 _ hnum valid668
  · exact recordValid_of_data section14Catalog 6 _ hnum valid669
  · exact recordValid_of_data section14Catalog 6 _ hnum valid670
  · exact recordValid_of_data section14Catalog 6 _ hnum valid671
end Section14Records_6_640_672

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0640_0672


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0672_0704
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_672_704
private theorem valid672 : RecordDataValid section14Catalog 6 (⟨35,(3),[1,2,5,6],[131],121⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨121,[1,2,3,5,6,7,9,10,11],121⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid673 : RecordDataValid section14Catalog 6 (⟨35,(4),[1,2,5,6],[130,131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid674 : RecordDataValid section14Catalog 6 (⟨35,(5),[1,2,5,6],[130,131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid675 : RecordDataValid section14Catalog 6 (⟨35,(6),[1,2,5,6],[131],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid676 : RecordDataValid section14Catalog 6 (⟨35,(6),[1,2,5,6],[150],140⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨140,[1,2,3,5,6,7],140⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid677 : RecordDataValid section14Catalog 6 (⟨35,(6),[2,6],[130],122⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨122,[1,2,3,5,6,7,9,10,11],122⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid678 : RecordDataValid section14Catalog 6 (⟨35,(6),[6],[146],1528⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1528,[6],1533⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid679 : RecordDataValid section14Catalog 6 (⟨35,(7),[1,2,5,6],[130,146,150],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid680 : RecordDataValid section14Catalog 6 (⟨35,(7),[1,2,5,6],[131],122⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨122,[1,2,3,5,6,7,9,10,11],122⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid681 : RecordDataValid section14Catalog 6 (⟨35,(8),[1,2,5,6],[130,131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid682 : RecordDataValid section14Catalog 6 (⟨35,(9),[1,2,5,6],[130,131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid683 : RecordDataValid section14Catalog 6 (⟨35,(10),[1,2,5,6],[131],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid684 : RecordDataValid section14Catalog 6 (⟨35,(10),[1,2,5,6],[150],141⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨141,[1,2,5,6],141⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid685 : RecordDataValid section14Catalog 6 (⟨35,(10),[2,6],[130],915⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨915,[2,6,10],918⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid686 : RecordDataValid section14Catalog 6 (⟨35,(10),[6],[146],1529⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1529,[6],1534⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid687 : RecordDataValid section14Catalog 6 (⟨35,(11),[1,2,5,6],[130,146,150],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid688 : RecordDataValid section14Catalog 6 (⟨35,(11),[1,2,5,6],[131],123⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨123,[1,2,5,6,9,10],123⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid689 : RecordDataValid section14Catalog 6 (⟨35,(12),[1,2,5,6],[130,131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid690 : RecordDataValid section14Catalog 6 (⟨35,(13),[1,2,5,6],[130,131,146,150],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid691 : RecordDataValid section14Catalog 6 (⟨35,(14),[1,2,5,6],[131],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid692 : RecordDataValid section14Catalog 6 (⟨35,(14),[1,2,5,6],[150],142⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨142,[1,2,3,5,6,7],142⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid693 : RecordDataValid section14Catalog 6 (⟨35,(14),[2,6],[130],124⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨124,[1,2,3,5,6,7,9,10,11],124⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid694 : RecordDataValid section14Catalog 6 (⟨35,(14),[6],[146],1530⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1530,[6],1535⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid695 : RecordDataValid section14Catalog 6 (⟨35,(15),[1,2,5,6],[130,146,150],101⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid696 : RecordDataValid section14Catalog 6 (⟨35,(15),[1,2,5,6],[131],124⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨124,[1,2,3,5,6,7,9,10,11],124⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid697 : RecordDataValid section14Catalog 6 (⟨36,(5),[1,2,5,6],[130],105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨105,[1,2,3,5,6,7,13,14,15],105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid698 : RecordDataValid section14Catalog 6 (⟨36,(5),[1,2,5,6,13,14],[131,146,150],105⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨105,[1,2,3,5,6,7,13,14,15],105⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid699 : RecordDataValid section14Catalog 6 (⟨36,(7),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid700 : RecordDataValid section14Catalog 6 (⟨36,(7),[1,2,5,6,13,14],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid701 : RecordDataValid section14Catalog 6 (⟨36,(7),[1,2,5,6,14],[131,146],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid702 : RecordDataValid section14Catalog 6 (⟨36,(8),[1,2,5,6,13,14],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid703 : RecordDataValid section14Catalog 6 (⟨36,(8),[1,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_0672_0704 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 672).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 672).take 32 = [⟨35,(3),[1,2,5,6],[131],121⟩,⟨35,(4),[1,2,5,6],[130,131,146,150],2⟩,⟨35,(5),[1,2,5,6],[130,131,146,150],2⟩,⟨35,(6),[1,2,5,6],[131],101⟩,⟨35,(6),[1,2,5,6],[150],140⟩,⟨35,(6),[2,6],[130],122⟩,⟨35,(6),[6],[146],1528⟩,⟨35,(7),[1,2,5,6],[130,146,150],101⟩,⟨35,(7),[1,2,5,6],[131],122⟩,⟨35,(8),[1,2,5,6],[130,131,146,150],2⟩,⟨35,(9),[1,2,5,6],[130,131,146,150],2⟩,⟨35,(10),[1,2,5,6],[131],101⟩,⟨35,(10),[1,2,5,6],[150],141⟩,⟨35,(10),[2,6],[130],915⟩,⟨35,(10),[6],[146],1529⟩,⟨35,(11),[1,2,5,6],[130,146,150],101⟩,⟨35,(11),[1,2,5,6],[131],123⟩,⟨35,(12),[1,2,5,6],[130,131,146,150],2⟩,⟨35,(13),[1,2,5,6],[130,131,146,150],2⟩,⟨35,(14),[1,2,5,6],[131],101⟩,⟨35,(14),[1,2,5,6],[150],142⟩,⟨35,(14),[2,6],[130],124⟩,⟨35,(14),[6],[146],1530⟩,⟨35,(15),[1,2,5,6],[130,146,150],101⟩,⟨35,(15),[1,2,5,6],[131],124⟩,⟨36,(5),[1,2,5,6],[130],105⟩,⟨36,(5),[1,2,5,6,13,14],[131,146,150],105⟩,⟨36,(7),[1,2,5,6],[130],3⟩,⟨36,(7),[1,2,5,6,13,14],[150],3⟩,⟨36,(7),[1,2,5,6,14],[131,146],3⟩,⟨36,(8),[1,2,5,6,13,14],[150],3⟩,⟨36,(8),[1,5,6],[130],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid672
  · exact recordValid_of_data section14Catalog 6 _ hnum valid673
  · exact recordValid_of_data section14Catalog 6 _ hnum valid674
  · exact recordValid_of_data section14Catalog 6 _ hnum valid675
  · exact recordValid_of_data section14Catalog 6 _ hnum valid676
  · exact recordValid_of_data section14Catalog 6 _ hnum valid677
  · exact recordValid_of_data section14Catalog 6 _ hnum valid678
  · exact recordValid_of_data section14Catalog 6 _ hnum valid679
  · exact recordValid_of_data section14Catalog 6 _ hnum valid680
  · exact recordValid_of_data section14Catalog 6 _ hnum valid681
  · exact recordValid_of_data section14Catalog 6 _ hnum valid682
  · exact recordValid_of_data section14Catalog 6 _ hnum valid683
  · exact recordValid_of_data section14Catalog 6 _ hnum valid684
  · exact recordValid_of_data section14Catalog 6 _ hnum valid685
  · exact recordValid_of_data section14Catalog 6 _ hnum valid686
  · exact recordValid_of_data section14Catalog 6 _ hnum valid687
  · exact recordValid_of_data section14Catalog 6 _ hnum valid688
  · exact recordValid_of_data section14Catalog 6 _ hnum valid689
  · exact recordValid_of_data section14Catalog 6 _ hnum valid690
  · exact recordValid_of_data section14Catalog 6 _ hnum valid691
  · exact recordValid_of_data section14Catalog 6 _ hnum valid692
  · exact recordValid_of_data section14Catalog 6 _ hnum valid693
  · exact recordValid_of_data section14Catalog 6 _ hnum valid694
  · exact recordValid_of_data section14Catalog 6 _ hnum valid695
  · exact recordValid_of_data section14Catalog 6 _ hnum valid696
  · exact recordValid_of_data section14Catalog 6 _ hnum valid697
  · exact recordValid_of_data section14Catalog 6 _ hnum valid698
  · exact recordValid_of_data section14Catalog 6 _ hnum valid699
  · exact recordValid_of_data section14Catalog 6 _ hnum valid700
  · exact recordValid_of_data section14Catalog 6 _ hnum valid701
  · exact recordValid_of_data section14Catalog 6 _ hnum valid702
  · exact recordValid_of_data section14Catalog 6 _ hnum valid703
end Section14Records_6_672_704

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0672_0704


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0704_0736
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_704_736
private theorem valid704 : RecordDataValid section14Catalog 6 (⟨36,(8),[1,5,6,13,14],[131,146],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid705 : RecordDataValid section14Catalog 6 (⟨36,(9),[1,2,5,6,13,14],[150],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid706 : RecordDataValid section14Catalog 6 (⟨36,(9),[2,5,6],[130],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid707 : RecordDataValid section14Catalog 6 (⟨36,(9),[2,5,6,14],[131,146],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid708 : RecordDataValid section14Catalog 6 (⟨36,(15),[1,2,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid709 : RecordDataValid section14Catalog 6 (⟨36,(15),[1,2,5,6,13,14],[131,146],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid710 : RecordDataValid section14Catalog 6 (⟨36,(15),[1,2,5,6,14],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid711 : RecordDataValid section14Catalog 6 (⟨36,(16),[1,2,5,6,13,14],[150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid712 : RecordDataValid section14Catalog 6 (⟨36,(16),[1,5,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid713 : RecordDataValid section14Catalog 6 (⟨36,(16),[1,5,6,13,14],[131,146],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid714 : RecordDataValid section14Catalog 6 (⟨36,(17),[1,2,6],[130],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid715 : RecordDataValid section14Catalog 6 (⟨36,(17),[1,2,6,14],[131,146,150],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid716 : RecordDataValid section14Catalog 6 (⟨36,(19),[5,6],[130],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid717 : RecordDataValid section14Catalog 6 (⟨36,(19),[5,6,13,14],[131,146,150],143⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨143,[1,2,3,5,6,7,8,9,10,12,13,14,15,16],143⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid718 : RecordDataValid section14Catalog 6 (⟨38,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],246⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨246,[1,2,3,5,6,7,9,10,11,13,14,15],246⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid719 : RecordDataValid section14Catalog 6 (⟨38,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid720 : RecordDataValid section14Catalog 6 (⟨38,(-1),[1,2,5,6,9,10,13,14],[5],246⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨246,[1,2,3,5,6,7,9,10,11,13,14,15],246⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid721 : RecordDataValid section14Catalog 6 (⟨38,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid722 : RecordDataValid section14Catalog 6 (⟨38,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid723 : RecordDataValid section14Catalog 6 (⟨38,(-1),[1,2,5,6,13,14],[41,57],60⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨60,[1,2,3,5,6,7,13,14,15],60⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid724 : RecordDataValid section14Catalog 6 (⟨38,(-1),[1,2,5,6,13,14],[45],61⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨61,[1,2,5,6,9,10,13,14],61⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid725 : RecordDataValid section14Catalog 6 (⟨38,(-1),[1,2,5,6,13,14],[104,120],67⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨67,[1,2,5,6,13,14],67⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid726 : RecordDataValid section14Catalog 6 (⟨38,(-1),[1,2,5,6,13,14],[105,121],68⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨68,[1,2,3,5,6,7,13,14,15],68⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid727 : RecordDataValid section14Catalog 6 (⟨38,(-1),[1,2,5,6,13,14],[108],69⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨69,[1,2,4,5,6,8,9,10,12,13,14,16],69⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid728 : RecordDataValid section14Catalog 6 (⟨38,(-1),[1,2,5,6,13,14],[109],70⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨70,[1,2,4,5,6,8,9,10,12,13,14,16],70⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid729 : RecordDataValid section14Catalog 6 (⟨38,(-1),[1,2,5,6,13,14],[171,187],206⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨206,[1,2,5,6,13,14],206⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid730 : RecordDataValid section14Catalog 6 (⟨38,(-1),[1,2,5,6,13,14],[175],207⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨207,[1,2,4,5,6,8,9,10,12,13,14,16],207⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid731 : RecordDataValid section14Catalog 6 (⟨38,(-1),[1,2,5,6,13,14],[234,250],243⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨243,[1,2,3,5,6,7,13,14,15],243⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid732 : RecordDataValid section14Catalog 6 (⟨38,(-1),[1,2,5,6,13,14],[238],244⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨244,[1,2,5,6,9,10,13,14],244⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid733 : RecordDataValid section14Catalog 6 (⟨38,(-1),[1,2,5,6,13,14],[17,21,61],246⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨246,[1,2,3,5,6,7,9,10,11,13,14,15],246⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid734 : RecordDataValid section14Catalog 6 (⟨38,(-1),[1,2,5,6,13,14],[64,68,80,84,124],247⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨247,[1,2,4,5,6,8,9,10,12,13,14,16],247⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid735 : RecordDataValid section14Catalog 6 (⟨38,(-1),[1,2,5,6,13,14],[65,69,81,85,125],248⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨248,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],248⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_0704_0736 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 704).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 704).take 32 = [⟨36,(8),[1,5,6,13,14],[131,146],3⟩,⟨36,(9),[1,2,5,6,13,14],[150],143⟩,⟨36,(9),[2,5,6],[130],143⟩,⟨36,(9),[2,5,6,14],[131,146],143⟩,⟨36,(15),[1,2,5,6],[130],3⟩,⟨36,(15),[1,2,5,6,13,14],[131,146],3⟩,⟨36,(15),[1,2,5,6,14],[150],3⟩,⟨36,(16),[1,2,5,6,13,14],[150],3⟩,⟨36,(16),[1,5,6],[130],3⟩,⟨36,(16),[1,5,6,13,14],[131,146],3⟩,⟨36,(17),[1,2,6],[130],3⟩,⟨36,(17),[1,2,6,14],[131,146,150],3⟩,⟨36,(19),[5,6],[130],143⟩,⟨36,(19),[5,6,13,14],[131,146,150],143⟩,⟨38,(-1),[1,2,3,5,6,7,9,10,13,14,15],[1],246⟩,⟨38,(-1),[1,2,5,6,9,10,13,14],[2,3,6,7,18,19,22,23],2⟩,⟨38,(-1),[1,2,5,6,9,10,13,14],[5],246⟩,⟨38,(-1),[1,2,5,6,13,14],[42,43,46,47,58,59,62,63,66,67,70,71,82,83,86,87,106,107,110,111,122,123,126,127,128,129,132,133,144,145,148,149,168,169,172,173,184,185,188,189,192,193,196,197,208,209,212,213,232,233,236,237,248,249,252,253],2⟩,⟨38,(-1),[1,2,5,6,13,14],[8,9,12,13,24,25,28,29,32,33,36,37,48,49,52,53,72,73,76,77,88,89,92,93,96,97,100,101,112,113,116,117,138,139,142,143,154,155,158,159,162,163,166,167,178,179,182,183,202,203,206,207,218,219,222,223,226,227,230,231,242,243,246,247],3⟩,⟨38,(-1),[1,2,5,6,13,14],[41,57],60⟩,⟨38,(-1),[1,2,5,6,13,14],[45],61⟩,⟨38,(-1),[1,2,5,6,13,14],[104,120],67⟩,⟨38,(-1),[1,2,5,6,13,14],[105,121],68⟩,⟨38,(-1),[1,2,5,6,13,14],[108],69⟩,⟨38,(-1),[1,2,5,6,13,14],[109],70⟩,⟨38,(-1),[1,2,5,6,13,14],[171,187],206⟩,⟨38,(-1),[1,2,5,6,13,14],[175],207⟩,⟨38,(-1),[1,2,5,6,13,14],[234,250],243⟩,⟨38,(-1),[1,2,5,6,13,14],[238],244⟩,⟨38,(-1),[1,2,5,6,13,14],[17,21,61],246⟩,⟨38,(-1),[1,2,5,6,13,14],[64,68,80,84,124],247⟩,⟨38,(-1),[1,2,5,6,13,14],[65,69,81,85,125],248⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid704
  · exact recordValid_of_data section14Catalog 6 _ hnum valid705
  · exact recordValid_of_data section14Catalog 6 _ hnum valid706
  · exact recordValid_of_data section14Catalog 6 _ hnum valid707
  · exact recordValid_of_data section14Catalog 6 _ hnum valid708
  · exact recordValid_of_data section14Catalog 6 _ hnum valid709
  · exact recordValid_of_data section14Catalog 6 _ hnum valid710
  · exact recordValid_of_data section14Catalog 6 _ hnum valid711
  · exact recordValid_of_data section14Catalog 6 _ hnum valid712
  · exact recordValid_of_data section14Catalog 6 _ hnum valid713
  · exact recordValid_of_data section14Catalog 6 _ hnum valid714
  · exact recordValid_of_data section14Catalog 6 _ hnum valid715
  · exact recordValid_of_data section14Catalog 6 _ hnum valid716
  · exact recordValid_of_data section14Catalog 6 _ hnum valid717
  · exact recordValid_of_data section14Catalog 6 _ hnum valid718
  · exact recordValid_of_data section14Catalog 6 _ hnum valid719
  · exact recordValid_of_data section14Catalog 6 _ hnum valid720
  · exact recordValid_of_data section14Catalog 6 _ hnum valid721
  · exact recordValid_of_data section14Catalog 6 _ hnum valid722
  · exact recordValid_of_data section14Catalog 6 _ hnum valid723
  · exact recordValid_of_data section14Catalog 6 _ hnum valid724
  · exact recordValid_of_data section14Catalog 6 _ hnum valid725
  · exact recordValid_of_data section14Catalog 6 _ hnum valid726
  · exact recordValid_of_data section14Catalog 6 _ hnum valid727
  · exact recordValid_of_data section14Catalog 6 _ hnum valid728
  · exact recordValid_of_data section14Catalog 6 _ hnum valid729
  · exact recordValid_of_data section14Catalog 6 _ hnum valid730
  · exact recordValid_of_data section14Catalog 6 _ hnum valid731
  · exact recordValid_of_data section14Catalog 6 _ hnum valid732
  · exact recordValid_of_data section14Catalog 6 _ hnum valid733
  · exact recordValid_of_data section14Catalog 6 _ hnum valid734
  · exact recordValid_of_data section14Catalog 6 _ hnum valid735
end Section14Records_6_704_736

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0704_0736


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0736_0768
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
namespace Section14Records_6_736_768
private theorem valid736 : RecordDataValid section14Catalog 6 (⟨38,(-1),[1,2,5,6,13,14],[130,134],249⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨249,[1,2,4,5,6,8,9,10,12,13,14,16],249⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid737 : RecordDataValid section14Catalog 6 (⟨38,(-1),[1,2,5,6,13,14],[146],250⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨250,[1,2,3,5,6,7,13,14,15],250⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid738 : RecordDataValid section14Catalog 6 (⟨38,(-1),[1,2,5,6,13,14],[147,151,191],251⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨251,[1,2,4,5,6,8,9,10,12,13,14,16],251⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid739 : RecordDataValid section14Catalog 6 (⟨38,(-1),[1,2,5,6,13,14],[210,214,254],340⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨340,[1,2,3,5,6,7,9,10,11,13,14,15],341⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid740 : RecordDataValid section14Catalog 6 (⟨38,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid741 : RecordDataValid section14Catalog 6 (⟨38,(-1),[1,5,6,13],[194,198],340⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨340,[1,2,3,5,6,7,9,10,11,13,14,15],341⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid742 : RecordDataValid section14Catalog 6 (⟨38,(-1),[2,4,6,8,10,12,14,16],[0,4],247⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨247,[1,2,4,5,6,8,9,10,12,13,14,16],247⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid743 : RecordDataValid section14Catalog 6 (⟨38,(-1),[2,6,9,10,14],[16,20],247⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨247,[1,2,4,5,6,8,9,10,12,13,14,16],247⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid744 : RecordDataValid section14Catalog 6 (⟨38,(-1),[2,6,14],[40,56],67⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨67,[1,2,5,6,13,14],67⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid745 : RecordDataValid section14Catalog 6 (⟨38,(-1),[2,6,14],[44],69⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨69,[1,2,4,5,6,8,9,10,12,13,14,16],69⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid746 : RecordDataValid section14Catalog 6 (⟨38,(-1),[2,6,14],[239],207⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨207,[1,2,4,5,6,8,9,10,12,13,14,16],207⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid747 : RecordDataValid section14Catalog 6 (⟨38,(-1),[2,6,14],[60],247⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨247,[1,2,4,5,6,8,9,10,12,13,14,16],247⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid748 : RecordDataValid section14Catalog 6 (⟨38,(-1),[2,6,14],[211,215,255],251⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨251,[1,2,4,5,6,8,9,10,12,13,14,16],251⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid749 : RecordDataValid section14Catalog 6 (⟨38,(-1),[2,6,14],[186],918⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨918,[2,6,14],921⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid750 : RecordDataValid section14Catalog 6 (⟨38,(-1),[5,6],[131,135],251⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨251,[1,2,4,5,6,8,9,10,12,13,14,16],251⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid751 : RecordDataValid section14Catalog 6 (⟨38,(-1),[6],[235,251],206⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨206,[1,2,5,6,13,14],206⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid752 : RecordDataValid section14Catalog 6 (⟨38,(-1),[6],[195,199],251⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨251,[1,2,4,5,6,8,9,10,12,13,14,16],251⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid753 : RecordDataValid section14Catalog 6 (⟨40,(0),[1,2,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid754 : RecordDataValid section14Catalog 6 (⟨40,(0),[6],[150],1532⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1532,[6,7,9,10,11],1537⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid755 : RecordDataValid section14Catalog 6 (⟨40,(1),[1,2,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid756 : RecordDataValid section14Catalog 6 (⟨40,(1),[6],[150],1532⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1532,[6,7,9,10,11],1537⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid757 : RecordDataValid section14Catalog 6 (⟨40,(2),[1,2,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid758 : RecordDataValid section14Catalog 6 (⟨40,(2),[6],[150],1532⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1532,[6,7,9,10,11],1537⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid759 : RecordDataValid section14Catalog 6 (⟨40,(3),[1,2,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid760 : RecordDataValid section14Catalog 6 (⟨40,(3),[6],[150],1532⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1532,[6,7,9,10,11],1537⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid761 : RecordDataValid section14Catalog 6 (⟨40,(4),[1,2,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid762 : RecordDataValid section14Catalog 6 (⟨40,(4),[6],[150],1532⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1532,[6,7,9,10,11],1537⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid763 : RecordDataValid section14Catalog 6 (⟨40,(5),[1,2,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid764 : RecordDataValid section14Catalog 6 (⟨40,(5),[6],[150],1533⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1533,[6,7,9,10,11],1538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid765 : RecordDataValid section14Catalog 6 (⟨40,(6),[1,2,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid766 : RecordDataValid section14Catalog 6 (⟨40,(6),[6],[150],1533⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨1533,[6,7,9,10,11],1538⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
private theorem valid767 : RecordDataValid section14Catalog 6 (⟨40,(7),[1,2,5,6,13,14],[170,174,190],3⟩) := by
  unfold RecordDataValid
  refine ⟨?_,?_,?_,?_,?_,?_,(⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩),?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_records_0736_0768 : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 736).take 32, section14RecordValid section14Catalog 6 r := by
  intro hnum
  have he : ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 736).take 32 = [⟨38,(-1),[1,2,5,6,13,14],[130,134],249⟩,⟨38,(-1),[1,2,5,6,13,14],[146],250⟩,⟨38,(-1),[1,2,5,6,13,14],[147,151,191],251⟩,⟨38,(-1),[1,2,5,6,13,14],[210,214,254],340⟩,⟨38,(-1),[1,2,5,6,14],[10,11,14,15,26,27,30,31,34,35,38,39,50,51,54,55,74,75,78,79,90,91,94,95,98,99,102,103,114,115,118,119,136,137,140,141,152,153,156,157,160,161,164,165,176,177,180,181,200,201,204,205,216,217,220,221,224,225,228,229,240,241,244,245],3⟩,⟨38,(-1),[1,5,6,13],[194,198],340⟩,⟨38,(-1),[2,4,6,8,10,12,14,16],[0,4],247⟩,⟨38,(-1),[2,6,9,10,14],[16,20],247⟩,⟨38,(-1),[2,6,14],[40,56],67⟩,⟨38,(-1),[2,6,14],[44],69⟩,⟨38,(-1),[2,6,14],[239],207⟩,⟨38,(-1),[2,6,14],[60],247⟩,⟨38,(-1),[2,6,14],[211,215,255],251⟩,⟨38,(-1),[2,6,14],[186],918⟩,⟨38,(-1),[5,6],[131,135],251⟩,⟨38,(-1),[6],[235,251],206⟩,⟨38,(-1),[6],[195,199],251⟩,⟨40,(0),[1,2,5,6,13,14],[170,174,190],3⟩,⟨40,(0),[6],[150],1532⟩,⟨40,(1),[1,2,5,6,13,14],[170,174,190],3⟩,⟨40,(1),[6],[150],1532⟩,⟨40,(2),[1,2,5,6,13,14],[170,174,190],3⟩,⟨40,(2),[6],[150],1532⟩,⟨40,(3),[1,2,5,6,13,14],[170,174,190],3⟩,⟨40,(3),[6],[150],1532⟩,⟨40,(4),[1,2,5,6,13,14],[170,174,190],3⟩,⟨40,(4),[6],[150],1532⟩,⟨40,(5),[1,2,5,6,13,14],[170,174,190],3⟩,⟨40,(5),[6],[150],1533⟩,⟨40,(6),[1,2,5,6,13,14],[170,174,190],3⟩,⟨40,(6),[6],[150],1533⟩,⟨40,(7),[1,2,5,6,13,14],[170,174,190],3⟩] := by decide +kernel
  rw [he]
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact recordValid_of_data section14Catalog 6 _ hnum valid736
  · exact recordValid_of_data section14Catalog 6 _ hnum valid737
  · exact recordValid_of_data section14Catalog 6 _ hnum valid738
  · exact recordValid_of_data section14Catalog 6 _ hnum valid739
  · exact recordValid_of_data section14Catalog 6 _ hnum valid740
  · exact recordValid_of_data section14Catalog 6 _ hnum valid741
  · exact recordValid_of_data section14Catalog 6 _ hnum valid742
  · exact recordValid_of_data section14Catalog 6 _ hnum valid743
  · exact recordValid_of_data section14Catalog 6 _ hnum valid744
  · exact recordValid_of_data section14Catalog 6 _ hnum valid745
  · exact recordValid_of_data section14Catalog 6 _ hnum valid746
  · exact recordValid_of_data section14Catalog 6 _ hnum valid747
  · exact recordValid_of_data section14Catalog 6 _ hnum valid748
  · exact recordValid_of_data section14Catalog 6 _ hnum valid749
  · exact recordValid_of_data section14Catalog 6 _ hnum valid750
  · exact recordValid_of_data section14Catalog 6 _ hnum valid751
  · exact recordValid_of_data section14Catalog 6 _ hnum valid752
  · exact recordValid_of_data section14Catalog 6 _ hnum valid753
  · exact recordValid_of_data section14Catalog 6 _ hnum valid754
  · exact recordValid_of_data section14Catalog 6 _ hnum valid755
  · exact recordValid_of_data section14Catalog 6 _ hnum valid756
  · exact recordValid_of_data section14Catalog 6 _ hnum valid757
  · exact recordValid_of_data section14Catalog 6 _ hnum valid758
  · exact recordValid_of_data section14Catalog 6 _ hnum valid759
  · exact recordValid_of_data section14Catalog 6 _ hnum valid760
  · exact recordValid_of_data section14Catalog 6 _ hnum valid761
  · exact recordValid_of_data section14Catalog 6 _ hnum valid762
  · exact recordValid_of_data section14Catalog 6 _ hnum valid763
  · exact recordValid_of_data section14Catalog 6 _ hnum valid764
  · exact recordValid_of_data section14Catalog 6 _ hnum valid765
  · exact recordValid_of_data section14Catalog 6 _ hnum valid766
  · exact recordValid_of_data section14Catalog 6 _ hnum valid767
end Section14Records_6_736_768

end WorkReverseInterface_Freiman_workReverse20260919_s0006_records_0736_0768

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
theorem _root_.solution : (∀ a ∈ section14Catalog.assignments, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId))) → ∀ r ∈ ((section14Catalog.records.filter (fun r => decide (6 ∈ r.states))).drop 640).take 128, section14RecordValid section14Catalog 6 r := by
  intro hnum
  let xs := (section14Catalog.records.filter (fun r => decide (6 ∈ r.states)))
  let P := fun r : Section14Record => section14RecordValid section14Catalog 6 r
  exact (all_of_interval_split P xs 640 704 768 (by decide) (by decide) (all_of_interval_split P xs 640 672 704 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_0640_0672 hnum) (Freiman.workReverse20260919_s0006_records_0672_0704 hnum)) (all_of_interval_split P xs 704 736 768 (by decide) (by decide) (Freiman.workReverse20260919_s0006_records_0704_0736 hnum) (Freiman.workReverse20260919_s0006_records_0736_0768 hnum)))

#print axioms solution
