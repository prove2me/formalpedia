-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LeftDerivativeCurves.ld_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:00:46.166258+00:00
-- url     : https://prove2.me/submissions/b4b51606-bb93-49b8-9860-4a48ca045019

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftDerivativeCurves
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftDerivativeCurves_l_hasDeriv_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.LeftDerivativeCurves
open Qx2 (Good)
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.LeftDerivativeCurves
theorem _root_.solution {f : Mx k r → E} (hf : SmoothLev k r i D f) {X : Mx k r} (hX : inLieLev k r i X) :
    SmoothLev k r i D (LdV X f) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, he⟩ := hf g₀ hg₀
  refine ⟨U, fun x => fderiv ℝ F x (X * x), hU, hgU, ?_, fun x hxU hx => ?_⟩
  · have h2 : ContDiffOn ℝ ∞ (fun x : Mx k r => X * x) U := (mulL X).contDiff.contDiffOn
    exact (hF.fderiv_of_isOpen hU (by simp)).clm_apply h2
  · have hFd : DifferentiableAt ℝ F x := (hF.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
    exact (l_hasDeriv_ext hU hxU hx hX hFd he).deriv
end Formalism.FourierDecayAlt.P.LeftDerivativeCurves
