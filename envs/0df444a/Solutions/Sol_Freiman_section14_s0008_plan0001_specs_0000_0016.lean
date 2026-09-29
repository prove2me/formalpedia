-- Prove2me | solution 1 for Freiman.section14_s0008_plan0001_specs_0000_0016
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T06:10:35.248323+00:00
-- url     : https://prove2.me/submissions/50e69b85-7e38-43fe-a41e-c6e9ddb5169d

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

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Specs_8_1_0_16
private theorem valid0 : section14SpecValid section14Catalog (section14State section14Catalog 8) 2 ((482,⟨([1],[]),true,([1],[]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid1 : section14SpecValid section14Catalog (section14State section14Catalog 8) 2 ((483,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩)) := by
  decide +kernel
private theorem valid2 : section14SpecValid section14Catalog (section14State section14Catalog 8) 2 ((484,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩)) := by
  decide +kernel
private theorem valid3 : section14SpecValid section14Catalog (section14State section14Catalog 8) 2 ((20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩)) := by
  decide +kernel
private theorem valid4 : section14SpecValid section14Catalog (section14State section14Catalog 8) 2 ((21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩)) := by
  decide +kernel
private theorem valid5 : section14SpecValid section14Catalog (section14State section14Catalog 8) 2 ((485,⟨([2],[]),true,([2],[]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid6 : section14SpecValid section14Catalog (section14State section14Catalog 8) 2 ((486,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩)) := by
  decide +kernel
private theorem valid7 : section14SpecValid section14Catalog (section14State section14Catalog 8) 2 ((487,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩)) := by
  decide +kernel
private theorem valid8 : section14SpecValid section14Catalog (section14State section14Catalog 8) 2 ((25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩)) := by
  decide +kernel
private theorem valid9 : section14SpecValid section14Catalog (section14State section14Catalog 8) 2 ((26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩)) := by
  decide +kernel
private theorem valid10 : section14SpecValid section14Catalog (section14State section14Catalog 8) 2 ((488,⟨([3],[]),true,([3],[]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid11 : section14SpecValid section14Catalog (section14State section14Catalog 8) 2 ((489,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩)) := by
  decide +kernel
private theorem valid12 : section14SpecValid section14Catalog (section14State section14Catalog 8) 2 ((490,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩)) := by
  decide +kernel
private theorem valid13 : section14SpecValid section14Catalog (section14State section14Catalog 8) 2 ((30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩)) := by
  decide +kernel
private theorem valid14 : section14SpecValid section14Catalog (section14State section14Catalog 8) 2 ((31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩)) := by
  decide +kernel
private theorem valid15 : section14SpecValid section14Catalog (section14State section14Catalog 8) 2 ((491,⟨([1],[]),true,([2],[]),false,false,[]⟩)) := by
  decide +kernel
theorem _root_.solution : ∀ gs ∈ (((section14State section14Catalog 8).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 16, section14SpecValid section14Catalog (section14State section14Catalog 8) ((section14State section14Catalog 8).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by
  have hp : ((section14State section14Catalog 8).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)) = (⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(482,⟨([1],[]),true,([1],[]),false,false,[]⟩),(483,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(484,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(485,⟨([2],[]),true,([2],[]),false,false,[]⟩),(486,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(487,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(488,⟨([3],[]),true,([3],[]),false,false,[]⟩),(489,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(490,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(491,⟨([1],[]),true,([2],[]),false,false,[]⟩),(492,⟨([2],[]),true,([1],[]),false,false,[]⟩),(493,⟨([2],[]),true,([3],[]),false,false,[]⟩),(494,⟨([3],[]),true,([2],[]),false,false,[]⟩),(495,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩ : Section14Plan) := by rfl
  rw [hp]
  change ∀ gs ∈ [(482,⟨([1],[]),true,([1],[]),false,false,[]⟩),(483,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(484,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(20,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(21,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(485,⟨([2],[]),true,([2],[]),false,false,[]⟩),(486,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(487,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(488,⟨([3],[]),true,([3],[]),false,false,[]⟩),(489,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(490,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(491,⟨([1],[]),true,([2],[]),false,false,[]⟩)], section14SpecValid section14Catalog (section14State section14Catalog 8) 2 gs
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
end Section14Specs_8_1_0_16

#print axioms solution
