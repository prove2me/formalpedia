-- Prove2me | solution 1 for Freiman.section14_s0011_plan0000_metadata
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T09:48:01.297193+00:00
-- url     : https://prove2.me/submissions/19b61c92-1d94-4937-bef4-a61fda151199

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
theorem _root_.solution : ((section14State section14Catalog 11).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).labels ≠ [] ∧ (section14Goal section14Catalog ((section14State section14Catalog 11).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).excludedGoal).first = 0 ∧ (section14Goal section14Catalog ((section14State section14Catalog 11).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).excludedGoal).second = 0 ∧ (section14Goal section14Catalog ((section14State section14Catalog 11).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).excludedGoal).caseId = ((section14State section14Catalog 11).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).caseId ∧ (section14Goal section14Catalog ((section14State section14Catalog 11).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).excludedGoal).extra = [] ∧ (((section14State section14Catalog 11).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).specs.map Prod.snd).toFinset = (section14ExpectedSpecs ((section14State section14Catalog 11).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).labels ((section14State section14Catalog 11).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)).targetLower).toFinset := by
  have hp : ((section14State section14Catalog 11).plans[0]?.getD (⟨0,0,[],false,[]⟩ : Section14Plan)) = (⟨1,1,[([1],[]),([],[1])],false,[(586,⟨([1],[]),true,([1],[]),false,false,[]⟩),(325,⟨([1,1],[]),true,([1,2],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(326,⟨([1,2],[]),true,([1,1],[]),false,true,[⟨false,false,section14DataThreshold 4⟩]⟩),(537,⟨([1],[1]),true,([1],[2]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(587,⟨([1],[2]),true,([1],[1]),false,true,[⟨true,true,section14DataThreshold 4⟩]⟩),(588,⟨([],[1]),true,([],[1]),false,false,[]⟩),(589,⟨([1],[1]),true,([2],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(330,⟨([2],[1]),true,([1],[1]),false,true,[⟨false,false,section14DataThreshold 46⟩]⟩),(541,⟨([],[1,1]),true,([],[1,2]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(542,⟨([],[1,2]),true,([],[1,1]),false,true,[⟨true,true,section14DataThreshold 46⟩]⟩),(590,⟨([1],[]),true,([],[1]),false,false,[]⟩),(591,⟨([],[1]),true,([1],[]),false,false,[]⟩),(545,⟨([1],[]),true,([],[]),true,false,[]⟩),(333,⟨([],[]),false,([],[1]),false,false,[]⟩)]⟩ : Section14Plan) := by rfl
  rw [hp]
  decide +kernel

#print axioms solution
