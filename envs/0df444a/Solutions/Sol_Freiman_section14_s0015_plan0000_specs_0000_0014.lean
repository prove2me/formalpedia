-- Prove2me | solution 1 for Freiman.section14_s0015_plan0000_specs_0000_0014
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T17:12:49.879665+00:00
-- url     : https://prove2.me/submissions/2d10bbb0-21ba-47ee-b7c4-8a262a3be92d

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
namespace Section14Specs_15_0_0_14
private theorem valid0 : section14SpecValid section14Catalog (section14State section14Catalog 15) 1 ((324,⟨([1],[]),true,([1],[]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid1 : section14SpecValid section14Catalog (section14State section14Catalog 15) 1 ((325,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩)) := by
  decide +kernel
private theorem valid2 : section14SpecValid section14Catalog (section14State section14Catalog 15) 1 ((326,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩)) := by
  decide +kernel
private theorem valid3 : section14SpecValid section14Catalog (section14State section14Catalog 15) 1 ((5,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩)) := by
  decide +kernel
private theorem valid4 : section14SpecValid section14Catalog (section14State section14Catalog 15) 1 ((327,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩)) := by
  decide +kernel
private theorem valid5 : section14SpecValid section14Catalog (section14State section14Catalog 15) 1 ((647,⟨([],[1]),true,([],[1]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid6 : section14SpecValid section14Catalog (section14State section14Catalog 15) 1 ((329,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩)) := by
  decide +kernel
private theorem valid7 : section14SpecValid section14Catalog (section14State section14Catalog 15) 1 ((330,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩)) := by
  decide +kernel
private theorem valid8 : section14SpecValid section14Catalog (section14State section14Catalog 15) 1 ((635,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩)) := by
  decide +kernel
private theorem valid9 : section14SpecValid section14Catalog (section14State section14Catalog 15) 1 ((636,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩)) := by
  decide +kernel
private theorem valid10 : section14SpecValid section14Catalog (section14State section14Catalog 15) 1 ((648,⟨([1],[]),true,([],[1]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid11 : section14SpecValid section14Catalog (section14State section14Catalog 15) 1 ((332,⟨([],[1]),true,([1],[]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid12 : section14SpecValid section14Catalog (section14State section14Catalog 15) 1 ((14,⟨([1],[]),true,([],[]),true,false,[]⟩)) := by
  decide +kernel
private theorem valid13 : section14SpecValid section14Catalog (section14State section14Catalog 15) 1 ((649,⟨([],[]),false,([],[1]),false,false,[]⟩)) := by
  decide +kernel
theorem _root_.solution : ∀ gs ∈ (((section14State section14Catalog 15).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 0).take 14, section14SpecValid section14Catalog (section14State section14Catalog 15) ((section14State section14Catalog 15).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by
  have hp : ((section14State section14Catalog 15).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)) = (⟨1,1,[([1],[]),([],[1])],false,[(324,⟨([1],[]),true,([1],[]),false,false,[]⟩),(325,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(326,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(5,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(327,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(647,⟨([],[1]),true,([],[1]),false,false,[]⟩),(329,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(330,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(635,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(636,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(648,⟨([1],[]),true,([],[1]),false,false,[]⟩),(332,⟨([],[1]),true,([1],[]),false,false,[]⟩),(14,⟨([1],[]),true,([],[]),true,false,[]⟩),(649,⟨([],[]),false,([],[1]),false,false,[]⟩)]⟩ : Section14Plan) := by rfl
  rw [hp]
  change ∀ gs ∈ [(324,⟨([1],[]),true,([1],[]),false,false,[]⟩),(325,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(326,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(5,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(327,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(647,⟨([],[1]),true,([],[1]),false,false,[]⟩),(329,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(330,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(635,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(636,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(648,⟨([1],[]),true,([],[1]),false,false,[]⟩),(332,⟨([],[1]),true,([1],[]),false,false,[]⟩),(14,⟨([1],[]),true,([],[]),true,false,[]⟩),(649,⟨([],[]),false,([],[1]),false,false,[]⟩)], section14SpecValid section14Catalog (section14State section14Catalog 15) 1 gs
  intro gs hgs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
  rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
end Section14Specs_15_0_0_14

#print axioms solution
