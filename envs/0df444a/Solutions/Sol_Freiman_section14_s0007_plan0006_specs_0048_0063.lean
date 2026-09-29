-- Prove2me | solution 1 for Freiman.section14_s0007_plan0006_specs_0048_0063
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T09:08:24.712249+00:00
-- url     : https://prove2.me/submissions/0386fed8-1063-487a-b277-05ed104c4387

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
namespace Section14Specs_7_6_48_63
private theorem valid48 : section14SpecValid section14Catalog (section14State section14Catalog 7) 9 ((462,⟨([3,3],[2,1,3]),true,([2],[2]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid49 : section14SpecValid section14Catalog (section14State section14Catalog 7) 9 ((463,⟨([3,3],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid50 : section14SpecValid section14Catalog (section14State section14Catalog 7) 9 ((464,⟨([3,3],[2,1,2]),true,([3,3],[2,1,3]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid51 : section14SpecValid section14Catalog (section14State section14Catalog 7) 9 ((465,⟨([3,3],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid52 : section14SpecValid section14Catalog (section14State section14Catalog 7) 9 ((466,⟨([3,2],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid53 : section14SpecValid section14Catalog (section14State section14Catalog 7) 9 ((467,⟨([3,2],[2,1,3]),true,([3,2],[2,1,2]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid54 : section14SpecValid section14Catalog (section14State section14Catalog 7) 9 ((468,⟨([3,2],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid55 : section14SpecValid section14Catalog (section14State section14Catalog 7) 9 ((469,⟨([3,2],[2,1,2]),true,([3,2],[2,1,1]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid56 : section14SpecValid section14Catalog (section14State section14Catalog 7) 9 ((470,⟨([3,2],[2,1,1]),true,([3,2],[2,1,2]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid57 : section14SpecValid section14Catalog (section14State section14Catalog 7) 9 ((471,⟨([3,2],[2,1,1]),true,([2],[1]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid58 : section14SpecValid section14Catalog (section14State section14Catalog 7) 9 ((472,⟨([2],[1]),true,([3,2],[2,1,1]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid59 : section14SpecValid section14Catalog (section14State section14Catalog 7) 9 ((473,⟨([2],[1]),true,([3],[1]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid60 : section14SpecValid section14Catalog (section14State section14Catalog 7) 9 ((474,⟨([3],[1]),true,([2],[1]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid61 : section14SpecValid section14Catalog (section14State section14Catalog 7) 9 ((475,⟨([1],[]),true,([],[]),true,false,[]⟩)) := by
  decide +kernel
private theorem valid62 : section14SpecValid section14Catalog (section14State section14Catalog 7) 9 ((476,⟨([],[]),false,([3],[1]),false,false,[]⟩)) := by
  decide +kernel
theorem _root_.solution : ∀ gs ∈ (((section14State section14Catalog 7).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 48).take 15, section14SpecValid section14Catalog (section14State section14Catalog 7) ((section14State section14Catalog 7).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by
  have hp : ((section14State section14Catalog 7).plans[6]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)) = (⟨9,413,[([1],[]),([2],[2]),([3,3],[2,1,3]),([3,3],[2,1,2]),([2,3],[2,1,3]),([2,3],[2,1,2]),([2,3],[2,1,1]),([2],[1]),([3],[1])],false,[(414,⟨([1],[]),true,([1],[]),false,false,[]⟩),(415,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(416,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(417,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(418,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(419,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(420,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(421,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(422,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(423,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(424,⟨([3,3],[2,1,3]),true,([3,3],[2,1,3]),false,false,[]⟩),(425,⟨([3,3,1],[2,1,3]),true,([3,3,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(426,⟨([3,3,2],[2,1,3]),true,([3,3,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 340⟩]⟩),(427,⟨([3,3],[2,1,3,1]),true,([3,3],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(428,⟨([3,3],[2,1,3,2]),true,([3,3],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 340⟩]⟩),(429,⟨([3,3],[2,1,2]),true,([3,3],[2,1,2]),false,false,[]⟩),(430,⟨([3,3,1],[2,1,2]),true,([3,3,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(431,⟨([3,3,2],[2,1,2]),true,([3,3,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 360⟩]⟩),(432,⟨([3,3],[2,1,2,1]),true,([3,3],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(433,⟨([3,3],[2,1,2,2]),true,([3,3],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 360⟩]⟩),(434,⟨([3,2],[2,1,3]),true,([3,2],[2,1,3]),false,false,[]⟩),(435,⟨([3,2,1],[2,1,3]),true,([3,2,2],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(436,⟨([3,2,2],[2,1,3]),true,([3,2,1],[2,1,3]),false,true,[⟨false,false,section14DataThreshold 382⟩]⟩),(437,⟨([3,2],[2,1,3,1]),true,([3,2],[2,1,3,2]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(438,⟨([3,2],[2,1,3,2]),true,([3,2],[2,1,3,1]),false,true,[⟨true,true,section14DataThreshold 382⟩]⟩),(439,⟨([3,2],[2,1,2]),true,([3,2],[2,1,2]),false,false,[]⟩),(440,⟨([3,2,1],[2,1,2]),true,([3,2,2],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(441,⟨([3,2,2],[2,1,2]),true,([3,2,1],[2,1,2]),false,true,[⟨false,false,section14DataThreshold 403⟩]⟩),(442,⟨([3,2],[2,1,2,1]),true,([3,2],[2,1,2,2]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(443,⟨([3,2],[2,1,2,2]),true,([3,2],[2,1,2,1]),false,true,[⟨true,true,section14DataThreshold 403⟩]⟩),(444,⟨([3,2],[2,1,1]),true,([3,2],[2,1,1]),false,false,[]⟩),(445,⟨([3,2,1],[2,1,1]),true,([3,2,2],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(446,⟨([3,2,2],[2,1,1]),true,([3,2,1],[2,1,1]),false,true,[⟨false,false,section14DataThreshold 432⟩]⟩),(447,⟨([3,2],[2,1,1,1]),true,([3,2],[2,1,1,2]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(448,⟨([3,2],[2,1,1,2]),true,([3,2],[2,1,1,1]),false,true,[⟨true,true,section14DataThreshold 432⟩]⟩),(449,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(450,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(451,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(452,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(453,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(454,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(455,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(456,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(457,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(458,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(459,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(460,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(461,⟨([2],[2]),true,([3,3],[2,1,3]),false,false,[]⟩),(462,⟨([3,3],[2,1,3]),true,([2],[2]),false,false,[]⟩),(463,⟨([3,3],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(464,⟨([3,3],[2,1,2]),true,([3,3],[2,1,3]),false,false,[]⟩),(465,⟨([3,3],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(466,⟨([3,2],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(467,⟨([3,2],[2,1,3]),true,([3,2],[2,1,2]),false,false,[]⟩),(468,⟨([3,2],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(469,⟨([3,2],[2,1,2]),true,([3,2],[2,1,1]),false,false,[]⟩),(470,⟨([3,2],[2,1,1]),true,([3,2],[2,1,2]),false,false,[]⟩),(471,⟨([3,2],[2,1,1]),true,([2],[1]),false,false,[]⟩),(472,⟨([2],[1]),true,([3,2],[2,1,1]),false,false,[]⟩),(473,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(474,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(475,⟨([1],[]),true,([],[]),true,false,[]⟩),(476,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩ : Section14Plan) := by rfl
  rw [hp]
  change ∀ gs ∈ [(462,⟨([3,3],[2,1,3]),true,([2],[2]),false,false,[]⟩),(463,⟨([3,3],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(464,⟨([3,3],[2,1,2]),true,([3,3],[2,1,3]),false,false,[]⟩),(465,⟨([3,3],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(466,⟨([3,2],[2,1,3]),true,([3,3],[2,1,2]),false,false,[]⟩),(467,⟨([3,2],[2,1,3]),true,([3,2],[2,1,2]),false,false,[]⟩),(468,⟨([3,2],[2,1,2]),true,([3,2],[2,1,3]),false,false,[]⟩),(469,⟨([3,2],[2,1,2]),true,([3,2],[2,1,1]),false,false,[]⟩),(470,⟨([3,2],[2,1,1]),true,([3,2],[2,1,2]),false,false,[]⟩),(471,⟨([3,2],[2,1,1]),true,([2],[1]),false,false,[]⟩),(472,⟨([2],[1]),true,([3,2],[2,1,1]),false,false,[]⟩),(473,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(474,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(475,⟨([1],[]),true,([],[]),true,false,[]⟩),(476,⟨([],[]),false,([3],[1]),false,false,[]⟩)], section14SpecValid section14Catalog (section14State section14Catalog 7) 9 gs
  intro gs hgs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
  rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid48
  · exact valid49
  · exact valid50
  · exact valid51
  · exact valid52
  · exact valid53
  · exact valid54
  · exact valid55
  · exact valid56
  · exact valid57
  · exact valid58
  · exact valid59
  · exact valid60
  · exact valid61
  · exact valid62
end Section14Specs_7_6_48_63

#print axioms solution
