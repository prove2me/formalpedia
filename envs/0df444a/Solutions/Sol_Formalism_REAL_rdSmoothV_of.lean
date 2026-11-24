-- Prove2me | solution 1 for Formalism.REAL.rdSmoothV_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:01:33.79251+00:00
-- url     : https://prove2.me/submissions/b7704ce4-b505-49ac-b0f6-738456e05a58

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
theorem _root_.solution (h : RdExtV) : RdSmoothV := by
  intro n ε E _ _ f X hf hX g0 hg0
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ →L[ℝ] E) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
  obtain ⟨U, F, hU, hg0U, hF, hfF⟩ := hf g0 hg0
  refine ⟨U, fun x => fderiv ℝ F x (x * X), hU, hg0U, ?_,
    fun x hx hxJ => h n ε E f F U x X hU hx hxJ hF hfF hX⟩
  have hF1 : ContDiffOn ℝ ∞ (fun y => fderiv ℝ F y) U :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hU).mp hF).2
  have hL : ContDiff ℝ ∞ (fun y : Matrix (Fin n) (Fin n) ℂ => y * X) :=
    (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)).contDiff
  exact hF1.clm_apply hL.contDiffOn
end Formalism.REAL
