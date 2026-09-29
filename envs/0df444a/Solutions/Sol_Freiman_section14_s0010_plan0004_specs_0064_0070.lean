-- Prove2me | solution 1 for Freiman.section14_s0010_plan0004_specs_0064_0070
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T16:01:37.736452+00:00
-- url     : https://prove2.me/submissions/9c946601-f525-4a69-92b8-be1f981e00d2

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
namespace Section14Specs_10_4_64_70
private theorem valid64 : section14SpecValid section14Catalog (section14State section14Catalog 10) 5 ((147,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid65 : section14SpecValid section14Catalog (section14State section14Catalog 10) 5 ((148,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid66 : section14SpecValid section14Catalog (section14State section14Catalog 10) 5 ((149,⟨([2],[1]),true,([3],[1]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid67 : section14SpecValid section14Catalog (section14State section14Catalog 10) 5 ((150,⟨([3],[1]),true,([2],[1]),false,false,[]⟩)) := by
  decide +kernel
private theorem valid68 : section14SpecValid section14Catalog (section14State section14Catalog 10) 5 ((565,⟨([1],[]),true,([],[]),true,false,[]⟩)) := by
  decide +kernel
private theorem valid69 : section14SpecValid section14Catalog (section14State section14Catalog 10) 5 ((152,⟨([],[]),false,([3],[1]),false,false,[]⟩)) := by
  decide +kernel
theorem _root_.solution : ∀ gs ∈ (((section14State section14Catalog 10).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.drop 64).take 6, section14SpecValid section14Catalog (section14State section14Catalog 10) ((section14State section14Catalog 10).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId gs := by
  have hp : ((section14State section14Catalog 10).plans[4]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)) = (⟨5,82,[([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3]),([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1]),([3],[1])],false,[(561,⟨([1],[]),true,([1],[]),false,false,[]⟩),(84,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(85,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(562,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(563,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(88,⟨([2],[2]),true,([2],[2]),false,false,[]⟩),(89,⟨([2,1],[2]),true,([2,2],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(90,⟨([2,2],[2]),true,([2,1],[2]),false,true,[⟨false,false,section14DataThreshold 79⟩]⟩),(91,⟨([2],[2,1]),true,([2],[2,2]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(92,⟨([2],[2,2]),true,([2],[2,1]),false,true,[⟨true,true,section14DataThreshold 79⟩]⟩),(93,⟨([3,2],[3,2]),true,([3,2],[3,2]),false,false,[]⟩),(94,⟨([3,2,1],[3,2]),true,([3,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(95,⟨([3,2,2],[3,2]),true,([3,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 134⟩]⟩),(96,⟨([3,2],[3,2,1]),true,([3,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(97,⟨([3,2],[3,2,2]),true,([3,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 134⟩]⟩),(98,⟨([3,2],[3,3]),true,([3,2],[3,3]),false,false,[]⟩),(99,⟨([3,2,1],[3,3]),true,([3,2,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(100,⟨([3,2,2],[3,3]),true,([3,2,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 155⟩]⟩),(101,⟨([3,2],[3,3,1]),true,([3,2],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(102,⟨([3,2],[3,3,2]),true,([3,2],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 155⟩]⟩),(103,⟨([3,1,1],[3,2]),true,([3,1,1],[3,2]),false,false,[]⟩),(104,⟨([3,1,1,1],[3,2]),true,([3,1,1,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(105,⟨([3,1,1,2],[3,2]),true,([3,1,1,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 169⟩]⟩),(106,⟨([3,1,1],[3,2,1]),true,([3,1,1],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(107,⟨([3,1,1],[3,2,2]),true,([3,1,1],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 169⟩]⟩),(108,⟨([3,1,1],[3,3]),true,([3,1,1],[3,3]),false,false,[]⟩),(109,⟨([3,1,1,1],[3,3]),true,([3,1,1,2],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(110,⟨([3,1,1,2],[3,3]),true,([3,1,1,1],[3,3]),false,true,[⟨false,false,section14DataThreshold 197⟩]⟩),(111,⟨([3,1,1],[3,3,1]),true,([3,1,1],[3,3,2]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(112,⟨([3,1,1],[3,3,2]),true,([3,1,1],[3,3,1]),false,true,[⟨true,true,section14DataThreshold 197⟩]⟩),(113,⟨([3,1,2],[3,2]),true,([3,1,2],[3,2]),false,false,[]⟩),(114,⟨([3,1,2,1],[3,2]),true,([3,1,2,2],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(115,⟨([3,1,2,2],[3,2]),true,([3,1,2,1],[3,2]),false,true,[⟨false,false,section14DataThreshold 218⟩]⟩),(116,⟨([3,1,2],[3,2,1]),true,([3,1,2],[3,2,2]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(117,⟨([3,1,2],[3,2,2]),true,([3,1,2],[3,2,1]),false,true,[⟨true,true,section14DataThreshold 218⟩]⟩),(118,⟨([2],[1,1]),true,([2],[1,1]),false,false,[]⟩),(119,⟨([2,1],[1,1]),true,([2,2],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(120,⟨([2,2],[1,1]),true,([2,1],[1,1]),false,true,[⟨false,false,section14DataThreshold 52⟩]⟩),(121,⟨([2],[1,1,1]),true,([2],[1,1,2]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(122,⟨([2],[1,1,2]),true,([2],[1,1,1]),false,true,[⟨true,true,section14DataThreshold 52⟩]⟩),(123,⟨([2],[1]),true,([2],[1]),false,false,[]⟩),(124,⟨([2,1],[1]),true,([2,2],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(125,⟨([2,2],[1]),true,([2,1],[1]),false,true,[⟨false,false,section14DataThreshold 50⟩]⟩),(126,⟨([2],[1,1]),true,([2],[1,2]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(127,⟨([2],[1,2]),true,([2],[1,1]),false,true,[⟨true,true,section14DataThreshold 50⟩]⟩),(128,⟨([3],[1]),true,([3],[1]),false,false,[]⟩),(129,⟨([3,1],[1]),true,([3,2],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(130,⟨([3,2],[1]),true,([3,1],[1]),false,true,[⟨false,false,section14DataThreshold 100⟩]⟩),(131,⟨([3],[1,1]),true,([3],[1,2]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(132,⟨([3],[1,2]),true,([3],[1,1]),false,true,[⟨true,true,section14DataThreshold 100⟩]⟩),(564,⟨([1],[]),true,([2],[2]),false,false,[]⟩),(134,⟨([2],[2]),true,([1],[]),false,false,[]⟩),(135,⟨([2],[2]),true,([3,2],[3,2]),false,false,[]⟩),(136,⟨([3,2],[3,2]),true,([2],[2]),false,false,[]⟩),(137,⟨([3,2],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(138,⟨([3,2],[3,3]),true,([3,2],[3,2]),false,false,[]⟩),(139,⟨([3,2],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(140,⟨([3,1,1],[3,2]),true,([3,2],[3,3]),false,false,[]⟩),(141,⟨([3,1,1],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(142,⟨([3,1,1],[3,3]),true,([3,1,1],[3,2]),false,false,[]⟩),(143,⟨([3,1,1],[3,3]),true,([3,1,2],[3,2]),false,false,[]⟩),(144,⟨([3,1,2],[3,2]),true,([3,1,1],[3,3]),false,false,[]⟩),(145,⟨([3,1,2],[3,2]),true,([2],[1,1]),false,false,[]⟩),(146,⟨([2],[1,1]),true,([3,1,2],[3,2]),false,false,[]⟩),(147,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(148,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(149,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(150,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(565,⟨([1],[]),true,([],[]),true,false,[]⟩),(152,⟨([],[]),false,([3],[1]),false,false,[]⟩)]⟩ : Section14Plan) := by rfl
  rw [hp]
  change ∀ gs ∈ [(147,⟨([2],[1,1]),true,([2],[1]),false,false,[]⟩),(148,⟨([2],[1]),true,([2],[1,1]),false,false,[]⟩),(149,⟨([2],[1]),true,([3],[1]),false,false,[]⟩),(150,⟨([3],[1]),true,([2],[1]),false,false,[]⟩),(565,⟨([1],[]),true,([],[]),true,false,[]⟩),(152,⟨([],[]),false,([3],[1]),false,false,[]⟩)], section14SpecValid section14Catalog (section14State section14Catalog 10) 5 gs
  intro gs hgs
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hgs
  rcases hgs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid64
  · exact valid65
  · exact valid66
  · exact valid67
  · exact valid68
  · exact valid69
end Section14Specs_10_4_64_70

#print axioms solution
