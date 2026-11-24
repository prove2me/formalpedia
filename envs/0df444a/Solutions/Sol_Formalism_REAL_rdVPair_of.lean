-- Prove2me | solution 1 for Formalism.REAL.rdVPair_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:01:35.264873+00:00
-- url     : https://prove2.me/submissions/4a3b7224-0ae0-46af-9172-9233d9b0da56

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_VectorComplexifiedDerivativeCommutator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.REAL
theorem _root_.solution (h : RdExtV) : RdVPair := by
  intro n ε E E' _ _ _ _ φ f X g hf hX hg
  have hsm : SmoothOnGV ε (fun x => φ (f x)) := by
    intro g0 hg0
    obtain ⟨U, F, hU, hg0U, hF, hfF⟩ := hf g0 hg0
    exact ⟨U, fun x => φ (F x), hU, hg0U, (φ.restrictScalars ℝ).contDiff.comp_contDiffOn hF,
      fun x hx hxJ => by simp only [hfF x hx hxJ]⟩
  refine ⟨hsm, ?_⟩
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp) g hgU).differentiableAt (hU.mem_nhds hgU)
  rw [h n ε E f F U g X hU hgU hg hF hfF hX,
    h n ε E' (fun x => φ (f x)) (fun x => φ (F x)) U g X hU hgU hg
      ((φ.restrictScalars ℝ).contDiff.comp_contDiffOn hF)
      (fun x hx hxJ => by simp only [hfF x hx hxJ]) hX]
  have hcomp : fderiv ℝ (fun x => φ (F x)) g = (φ.restrictScalars ℝ).comp (fderiv ℝ F g) :=
    ((φ.restrictScalars ℝ).hasFDerivAt.comp g hd.hasFDerivAt).fderiv
  rw [hcomp]
  rfl
end Formalism.REAL
