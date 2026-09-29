-- Prove2me | solution 1 for Freiman.section14_s0012_plan0001_metadata
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-19T03:38:41.354669+00:00
-- url     : https://prove2.me/submissions/b1e54baa-8eb4-4684-843e-d98bac8d30a0

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
theorem _root_.solution : ((section14State section14Catalog 12).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).labels ≠ [] ∧ (section14Goal section14Catalog ((section14State section14Catalog 12).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).excludedGoal).first = 0 ∧ (section14Goal section14Catalog ((section14State section14Catalog 12).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).excludedGoal).second = 0 ∧ (section14Goal section14Catalog ((section14State section14Catalog 12).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).excludedGoal).caseId = ((section14State section14Catalog 12).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId ∧ (section14Goal section14Catalog ((section14State section14Catalog 12).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).excludedGoal).extra = [] ∧ (((section14State section14Catalog 12).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.map Prod.snd).toFinset = (section14ExpectedSpecs ((section14State section14Catalog 12).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).labels ((section14State section14Catalog 12).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).targetLower).toFinset := by
  have hp : ((section14State section14Catalog 12).plans[1]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)) = (⟨2,16,[([1],[]),([2],[]),([3],[])],false,[(613,⟨([1],[]),true,([1],[]),false,false,[]⟩),(483,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(484,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(547,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(548,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(485,⟨([2],[]),true,([2],[]),false,false,[]⟩),(486,⟨([2,1],[]),true,([2,2],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(487,⟨([2,2],[]),true,([2,1],[]),false,true,[⟨false,false,section14DataThreshold 1⟩]⟩),(25,⟨([2],[1]),true,([2],[2]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(26,⟨([2],[2]),true,([2],[1]),false,true,[⟨true,true,section14DataThreshold 1⟩]⟩),(488,⟨([3],[]),true,([3],[]),false,false,[]⟩),(489,⟨([3,1],[]),true,([3,2],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(490,⟨([3,2],[]),true,([3,1],[]),false,true,[⟨false,false,section14DataThreshold 86⟩]⟩),(30,⟨([3],[1]),true,([3],[2]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(31,⟨([3],[2]),true,([3],[1]),false,true,[⟨true,true,section14DataThreshold 86⟩]⟩),(614,⟨([1],[]),true,([2],[]),false,false,[]⟩),(492,⟨([2],[]),true,([1],[]),false,false,[]⟩),(493,⟨([2],[]),true,([3],[]),false,false,[]⟩),(494,⟨([3],[]),true,([2],[]),false,false,[]⟩),(615,⟨([1],[]),true,([],[]),true,false,[]⟩),(37,⟨([],[]),false,([3],[]),false,false,[]⟩)]⟩ : Section14Plan) := by rfl
  rw [hp]
  decide +kernel

#print axioms solution
