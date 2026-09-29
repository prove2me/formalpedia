-- Prove2me | solution 1 for Freiman.section14_s0008_plan0002_specs_0016_0021
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T06:14:41.906767+00:00
-- url     : https://prove2.me/submissions/e675c327-5674-45a0-ae08-27e7f879000a

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
namespace Section14Specs_8_2_16_21
private theorem valid16 : section14SpecValid section14Catalog (section14State section14Catalog 8) 3 ((503,⟨([2],[]),true,([1],[]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid17 : section14SpecValid section14Catalog (section14State section14Catalog 8) 3 ((504,⟨([2],[]),true,([3],[1]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid18 : section14SpecValid section14Catalog (section14State section14Catalog 8) 3 ((57,⟨([3],[1]),true,([2],[]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid19 : section14SpecValid section14Catalog (section14State section14Catalog 8) 3 ((505,⟨([1],[]),true,([],[]),true,false,[]⟩)) := by
  decide +kernel
private theorem valid20 : section14SpecValid section14Catalog (section14State section14Catalog 8) 3 ((59,⟨([],[]),false,([3],[1]),false,false,[]⟩)) := by
  decide +kernel
theorem _root_.solution : ∀ gs ∈ (((section14State section14Catalog 8).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 16).take 5, section14SpecValid section14Catalog (section14State section14Catalog 8) ((section14State section14Catalog 8).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by
  have hp : ((section14State section14Catalog 8).plans[2]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)) = (⟨3,38,[([1],[]),([2],[]),([3],[1])],false,[(496,⟨([1],[]),true,([1],[]),false,false,[]⟩),(497,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(498,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(42,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(43,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(499,⟨([2],[]),true,([2],[]),false,false,[]⟩),(500,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(501,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(47,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(48,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(49,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(50,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(51,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(52,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(53,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(502,⟨([1],[]),true,([2],[]),false,false,[]⟩),(503,⟨([2],[]),true,([1],[]),false,false,[]⟩),(504,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(57,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(505,⟨([1],[]),true,([],[]),true,false,[]⟩),(59,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩ : Section14Plan) := by rfl
  rw [hp]
  change ∀ gs ∈ [(503,⟨([2],[]),true,([1],[]),false,false,[]⟩),(504,⟨([2],[]),true,([3],[1]),false,false,[]⟩),(57,⟨([3],[1]),true,([2],[]),false,false,[]⟩),(505,⟨([1],[]),true,([],[]),true,false,[]⟩),(59,⟨([],[]),false,([3],[1]),false,false,[]⟩)], section14SpecValid section14Catalog (section14State section14Catalog 8) 3 gs
  intro gs hgs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
  rcases hgs with rfl | rfl | rfl | rfl | rfl
  · exact valid16
  · exact valid17
  · exact valid18
  · exact valid19
  · exact valid20
end Section14Specs_8_2_16_21

#print axioms solution
