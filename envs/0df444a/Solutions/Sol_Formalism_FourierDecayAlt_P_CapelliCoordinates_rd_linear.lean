-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliCoordinates.rd_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:48:20.228031+00:00
-- url     : https://prove2.me/submissions/5699f489-50a3-461f-ac36-1d28c51688e1

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliCoordinates
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_hasDeriv_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_rd_hasDeriv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.CapelliCoordinates
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.CapelliCoordinates
theorem _root_.solution {F : Mx k r → E} (hF : SmoothLev k r i D F) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    ∃ L : Mx k r →ₗ[ℝ] E, ∀ X, inLieLev k r i X → RdV X F g = L X := by
  obtain ⟨U, G, hU, hgU, hG, he⟩ := hF g hg
  have hGd : DifferentiableAt ℝ G g :=
    (hG.contDiffAt (hU.mem_nhds hgU)).differentiableAt (by simp)
  refine ⟨(fderiv ℝ G g).toLinearMap ∘ₗ LinearMap.mulLeft ℝ g, fun X hX => ?_⟩
  have h1 := Qx2.rd_hasDeriv hF hg hX
  have h2 := Qx2.hasDeriv_ext hU hgU hg.1 hX hGd he
  rw [h1.unique h2]
  rfl
end Formalism.FourierDecayAlt.P.CapelliCoordinates
