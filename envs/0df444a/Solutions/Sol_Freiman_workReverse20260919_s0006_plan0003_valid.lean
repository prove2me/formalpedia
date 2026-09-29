-- Prove2me | solution 1 for Freiman.workReverse20260919_s0006_plan0003_valid
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T20:33:47.706729+00:00
-- url     : https://prove2.me/submissions/246a503f-e787-4091-a252-49e8c3d40150

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_plan0003_specs_0000_0016
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Specs_6_3_0_16
private theorem valid0 : section14SpecValid section14Catalog (section14State section14Catalog 6) 4 ((61,⟨([1],[]),true,([1],[]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid1 : section14SpecValid section14Catalog (section14State section14Catalog 6) 4 ((62,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩)) := by
  decide +kernel
private theorem valid2 : section14SpecValid section14Catalog (section14State section14Catalog 6) 4 ((63,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩)) := by
  decide +kernel
private theorem valid3 : section14SpecValid section14Catalog (section14State section14Catalog 6) 4 ((64,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩)) := by
  decide +kernel
private theorem valid4 : section14SpecValid section14Catalog (section14State section14Catalog 6) 4 ((65,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩)) := by
  decide +kernel
private theorem valid5 : section14SpecValid section14Catalog (section14State section14Catalog 6) 4 ((66,⟨([2],[]),true,([2],[]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid6 : section14SpecValid section14Catalog (section14State section14Catalog 6) 4 ((67,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩)) := by
  decide +kernel
private theorem valid7 : section14SpecValid section14Catalog (section14State section14Catalog 6) 4 ((68,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩)) := by
  decide +kernel
private theorem valid8 : section14SpecValid section14Catalog (section14State section14Catalog 6) 4 ((69,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩)) := by
  decide +kernel
private theorem valid9 : section14SpecValid section14Catalog (section14State section14Catalog 6) 4 ((70,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩)) := by
  decide +kernel
private theorem valid10 : section14SpecValid section14Catalog (section14State section14Catalog 6) 4 ((71,⟨([3],[1]),true,([3],[1]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid11 : section14SpecValid section14Catalog (section14State section14Catalog 6) 4 ((72,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩)) := by
  decide +kernel
private theorem valid12 : section14SpecValid section14Catalog (section14State section14Catalog 6) 4 ((73,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩)) := by
  decide +kernel
private theorem valid13 : section14SpecValid section14Catalog (section14State section14Catalog 6) 4 ((74,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩)) := by
  decide +kernel
private theorem valid14 : section14SpecValid section14Catalog (section14State section14Catalog 6) 4 ((75,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩)) := by
  decide +kernel
private theorem valid15 : section14SpecValid section14Catalog (section14State section14Catalog 6) 4 ((76,⟨([1],[]),true,([2],[]),false,false,[]⟩)) := by
  decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_plan0003_specs_0000_0016 : ∀ gs ∈ (((section14State section14Catalog 6).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 16, section14SpecValid section14Catalog (section14State section14Catalog 6) ((section14State section14Catalog 6).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by
  have hp : ((section14State section14Catalog 6).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)) = (⟨4,60,[([1],[]),([2],[]),([3],[1])],false,[(61,⟨([1],[]),true,([1],[]),false,false,[]⟩),(62,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(63,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(64,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(65,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(66,⟨([2],[]),true,([2],[]),false,false,[]⟩),(67,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(68,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(69,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(70,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(71,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(72,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(73,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(74,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(75,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(76,⟨([1],[]),true,([2],[]),false,false,[]⟩),(77,⟨([2],[]),true,([1],[]),false,false,[]⟩),(78,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(79,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(80,⟨([1],[]),true,([],[]),true,false,[]⟩),(81,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩ : Section14Plan) := by rfl
  rw [hp]
  change ∀ gs ∈ [(61,⟨([1],[]),true,([1],[]),false,false,[]⟩),(62,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(63,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(64,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(65,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(66,⟨([2],[]),true,([2],[]),false,false,[]⟩),(67,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(68,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(69,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(70,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(71,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(72,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(73,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(74,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(75,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(76,⟨([1],[]),true,([2],[]),false,false,[]⟩)], section14SpecValid section14Catalog (section14State section14Catalog 6) 4 gs
  intro gs hgs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
  rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid0
  · exact valid1
  · exact valid2
  · exact valid3
  · exact valid4
  · exact valid5
  · exact valid6
  · exact valid7
  · exact valid8
  · exact valid9
  · exact valid10
  · exact valid11
  · exact valid12
  · exact valid13
  · exact valid14
  · exact valid15
end Section14Specs_6_3_0_16

end WorkReverseInterface_Freiman_workReverse20260919_s0006_plan0003_specs_0000_0016


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_plan0003_specs_0016_0021
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Specs_6_3_16_21
private theorem valid16 : section14SpecValid section14Catalog (section14State section14Catalog 6) 4 ((77,⟨([2],[]),true,([1],[]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid17 : section14SpecValid section14Catalog (section14State section14Catalog 6) 4 ((78,⟨([2],[]),true,([3],[1]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid18 : section14SpecValid section14Catalog (section14State section14Catalog 6) 4 ((79,⟨([3],[1]),true,([2],[]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid19 : section14SpecValid section14Catalog (section14State section14Catalog 6) 4 ((80,⟨([1],[]),true,([],[]),true,false,[]⟩)) := by
  decide +kernel
private theorem valid20 : section14SpecValid section14Catalog (section14State section14Catalog 6) 4 ((81,⟨([],[]),false,([3],[1]),false,false,[]⟩)) := by
  decide +kernel
theorem _root_.Freiman.workReverse20260919_s0006_plan0003_specs_0016_0021 : ∀ gs ∈ (((section14State section14Catalog 6).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 16).take 5, section14SpecValid section14Catalog (section14State section14Catalog 6) ((section14State section14Catalog 6).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by
  have hp : ((section14State section14Catalog 6).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)) = (⟨4,60,[([1],[]),([2],[]),([3],[1])],false,[(61,⟨([1],[]),true,([1],[]),false,false,[]⟩),(62,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(63,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(64,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(65,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(66,⟨([2],[]),true,([2],[]),false,false,[]⟩),(67,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(68,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(69,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(70,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(71,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(72,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(73,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(74,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(75,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(76,⟨([1],[]),true,([2],[]),false,false,[]⟩),(77,⟨([2],[]),true,([1],[]),false,false,[]⟩),(78,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(79,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(80,⟨([1],[]),true,([],[]),true,false,[]⟩),(81,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩ : Section14Plan) := by rfl
  rw [hp]
  change ∀ gs ∈ [(77,⟨([2],[]),true,([1],[]),false,false,[]⟩),(78,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(79,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(80,⟨([1],[]),true,([],[]),true,false,[]⟩),(81,⟨([],[]),false,([3],[1]),false,false,[]⟩)], section14SpecValid section14Catalog (section14State section14Catalog 6) 4 gs
  intro gs hgs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
  rcases hgs with rfl | rfl | rfl | rfl | rfl
  · exact valid16
  · exact valid17
  · exact valid18
  · exact valid19
  · exact valid20
end Section14Specs_6_3_16_21

end WorkReverseInterface_Freiman_workReverse20260919_s0006_plan0003_specs_0016_0021

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


namespace WorkReverseInterface_Freiman_workReverse20260919_s0006_plan0003_metadata
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
theorem _root_.Freiman.workReverse20260919_s0006_plan0003_metadata : ((section14State section14Catalog 6).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).labels ≠ [] ∧ (section14Goal section14Catalog ((section14State section14Catalog 6).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).excludedGoal).first = 0 ∧ (section14Goal section14Catalog ((section14State section14Catalog 6).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).excludedGoal).second = 0 ∧ (section14Goal section14Catalog ((section14State section14Catalog 6).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).excludedGoal).caseId = ((section14State section14Catalog 6).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId ∧ (section14Goal section14Catalog ((section14State section14Catalog 6).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).excludedGoal).extra = [] ∧ (((section14State section14Catalog 6).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.map Prod.snd).toFinset = (section14ExpectedSpecs ((section14State section14Catalog 6).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).labels ((section14State section14Catalog 6).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).targetLower).toFinset := by
  have hp : ((section14State section14Catalog 6).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)) = (⟨4,60,[([1],[]),([2],[]),([3],[1])],false,[(61,⟨([1],[]),true,([1],[]),false,false,[]⟩),(62,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(63,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(64,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(65,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(66,⟨([2],[]),true,([2],[]),false,false,[]⟩),(67,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(68,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(69,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(70,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(71,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(72,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(73,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(74,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(75,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(76,⟨([1],[]),true,([2],[]),false,false,[]⟩),(77,⟨([2],[]),true,([1],[]),false,false,[]⟩),(78,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(79,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(80,⟨([1],[]),true,([],[]),true,false,[]⟩),(81,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩ : Section14Plan) := by rfl
  rw [hp]
  decide +kernel

end WorkReverseInterface_Freiman_workReverse20260919_s0006_plan0003_metadata

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7Section14Sep18
theorem _root_.Freiman.workReverse20260919_s0006_plan0003_specs_all : ∀ gs ∈ ((section14State section14Catalog 6).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs, section14SpecValid section14Catalog (section14State section14Catalog 6) ((section14State section14Catalog 6).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by
  let xs := ((section14State section14Catalog 6).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs
  let P := fun gs : ℕ × Section14Spec => section14SpecValid section14Catalog (section14State section14Catalog 6) ((section14State section14Catalog 6).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs
  have h21 : ∀ x ∈ xs.drop 21, P x := by
    apply all_empty P _
    rfl
  have h16 : ∀ x ∈ xs.drop 16, P x := by
    apply all_of_chunks P xs 16 5 (Freiman.workReverse20260919_s0006_plan0003_specs_0016_0021)
    exact h21
  have h0 : ∀ x ∈ xs.drop 0, P x := by
    apply all_of_chunks P xs 0 16 (Freiman.workReverse20260919_s0006_plan0003_specs_0000_0016)
    exact h16
  simpa only [List.drop_zero] using h0

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
theorem _root_.solution : ∀ p ∈ ((section14State section14Catalog 6).plans.drop 3).take 1, section14PlanValid section14Catalog (section14State section14Catalog 6) p := by
  have hs : ((section14State section14Catalog 6).plans.drop 3).take 1 = [((section14State section14Catalog 6).plans[3]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan))] := by rfl
  rw [hs]
  intro pl hpl
  have he := List.mem_singleton.mp hpl
  subst pl
  rcases Freiman.workReverse20260919_s0006_plan0003_metadata with ⟨h0,h1,h2,h3,h4,h5⟩
  exact ⟨h0,h1,h2,h3,h4,h5,Freiman.workReverse20260919_s0006_plan0003_specs_all⟩

#print axioms solution
