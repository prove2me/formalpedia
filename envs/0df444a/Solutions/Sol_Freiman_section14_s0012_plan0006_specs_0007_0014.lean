-- Prove2me | solution 1 for Freiman.section14_s0012_plan0006_specs_0007_0014
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T04:07:40.13168+00:00
-- url     : https://prove2.me/submissions/5926b1cc-2c38-4070-a353-8b89205baa85

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
namespace Section14Specs_12_6_7_14
private theorem valid7 : section14SpecValid section14Catalog (section14State section14Catalog 12) 7 ((253,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩)) := by
  decide +kernel
private theorem valid8 : section14SpecValid section14Catalog (section14State section14Catalog 12) 7 ((576,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩)) := by
  decide +kernel
private theorem valid9 : section14SpecValid section14Catalog (section14State section14Catalog 12) 7 ((577,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩)) := by
  decide +kernel
private theorem valid10 : section14SpecValid section14Catalog (section14State section14Catalog 12) 7 ((629,⟨([1],[]),true,([],[1]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid11 : section14SpecValid section14Catalog (section14State section14Catalog 12) 7 ((579,⟨([],[1]),true,([1],[]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid12 : section14SpecValid section14Catalog (section14State section14Catalog 12) 7 ((630,⟨([1],[]),true,([],[]),true,false,[]⟩)) := by
  decide +kernel
private theorem valid13 : section14SpecValid section14Catalog (section14State section14Catalog 12) 7 ((259,⟨([],[]),false,([],[1]),false,false,[]⟩)) := by
  decide +kernel
theorem _root_.solution : ∀ gs ∈ (((section14State section14Catalog 12).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 7).take 7, section14SpecValid section14Catalog (section14State section14Catalog 12) ((section14State section14Catalog 12).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by
  have hp : ((section14State section14Catalog 12).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)) = (⟨7,245,[([1],[]),([],[1])],false,[(628,⟨([1],[]),true,([1],[]),false,false,[]⟩),(527,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(528,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(572,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(573,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(574,⟨([],[1]),true,([],[1]),false,false,[]⟩),(575,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(253,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(576,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(577,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(629,⟨([1],[]),true,([],[1]),false,false,[]⟩),(579,⟨([],[1]),true,([1],[]),false,false,[]⟩),(630,⟨([1],[]),true,([],[]),true,false,[]⟩),(259,⟨([],[]),false,([],[1]),false,false,[]⟩)]⟩ : Section14Plan) := by rfl
  rw [hp]
  change ∀ gs ∈ [(253,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(576,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(577,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(629,⟨([1],[]),true,([],[1]),false,false,[]⟩),(579,⟨([],[1]),true,([1],[]),false,false,[]⟩),(630,⟨([1],[]),true,([],[]),true,false,[]⟩),(259,⟨([],[]),false,([],[1]),false,false,[]⟩)], section14SpecValid section14Catalog (section14State section14Catalog 12) 7 gs
  intro gs hgs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
  rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid7
  · exact valid8
  · exact valid9
  · exact valid10
  · exact valid11
  · exact valid12
  · exact valid13
end Section14Specs_12_6_7_14

#print axioms solution
