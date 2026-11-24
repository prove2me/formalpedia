-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.rd_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:11:10.665989+00:00
-- url     : https://prove2.me/submissions/8d6ad122-65d7-46c4-849d-c988788957ea

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hasDeriv_ext

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
open Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.Qx2
theorem _root_.solution {f : Mx k r → E} (hf : SmoothLev k r i D f) {X : Mx k r} (hX : inLieLev k r i X) :
    SmoothLev k r i D (RdV X f) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, he⟩ := hf g₀ hg₀
  refine ⟨U, fun x => fderiv ℝ F x (x * X), hU, hgU, ?_, ?_⟩
  · have h1 := hF.fderiv_of_isOpen (m := ∞) hU (by simp)
    exact h1.clm_apply (mulRightRealCLM X).contDiff.contDiffOn
  · intro x hx hxG
    have hd : DifferentiableAt ℝ F x := (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
    exact (hasDeriv_ext hU hx hxG hX hd he).deriv
end Formalism.FourierDecayAlt.P.Qx2
