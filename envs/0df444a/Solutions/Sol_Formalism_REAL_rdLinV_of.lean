-- Prove2me | solution 1 for Formalism.REAL.rdLinV_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:03:14.750656+00:00
-- url     : https://prove2.me/submissions/f148adff-383a-4617-9dca-a7c611b4da2e

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_VectorComplexifiedDerivativeCommutator
import Theorems.Thm_Formalism_REAL_lie_algebra_add_mem
import Theorems.Thm_Formalism_REAL_lie_algebra_real_smul_mem


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
theorem _root_.solution (h : RdExtV) : RdLinV := by
  intro n ε E _ _ f f' X Y r c g hf hf' hX hY hg
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g hg
  have hFd : DifferentiableAt ℝ F g :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  have hFd' : DifferentiableAt ℝ F' g :=
    (hF'.differentiableOn (by simp)).differentiableAt (hU'.mem_nhds hgU')
  have eX := h n ε E f F U g X hU hgU hg hF hfF hX
  refine ⟨?_, ?_, ?_⟩
  · rw [h n ε E f F U g (X + Y) hU hgU hg hF hfF (lie_algebra_add_mem ε hX hY), eX,
      h n ε E f F U g Y hU hgU hg hF hfF hY, Matrix.mul_add, map_add]
  · rw [h n ε E f F U g ((r : ℂ) • X) hU hgU hg hF hfF (lie_algebra_real_smul_mem ε hX r), eX,
      Matrix.mul_smul, Complex.coe_smul, map_smul, Complex.coe_smul]
  · have hsm : ContDiffOn ℝ ∞ (fun x => F x + c • F' x) (U ∩ U') :=
      (hF.mono Set.inter_subset_left).add ((hF'.mono Set.inter_subset_right).const_smul c)
    rw [h n ε E (fun x => f x + c • f' x) (fun x => F x + c • F' x) (U ∩ U') g X (hU.inter hU')
      ⟨hgU, hgU'⟩ hg hsm (fun x hx hxJ => by rw [hfF x hx.1 hxJ, hfF' x hx.2 hxJ]) hX,
      eX, h n ε E f' F' U' g X hU' hgU' hg hF' hfF' hX]
    have hD : HasFDerivAt (fun x => F x + c • F' x) (fderiv ℝ F g + c • fderiv ℝ F' g) g :=
      hFd.hasFDerivAt.add (hFd'.hasFDerivAt.const_smul c)
    rw [hD.fderiv]
    simp
end Formalism.REAL
