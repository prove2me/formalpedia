-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBG.AAop_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:08:29.913034+00:00
-- url     : https://prove2.me/submissions/e8148593-c351-45f9-b4be-365f7dcbab8b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBGLet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BaseIndexConstantInjective
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBG_qminorOp_loc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBG
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Qx5 Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {D : Set (Q.Mx k r)}
namespace Formalism.FourierDecayAlt.P.PBG
theorem _root_.solution (hD : IsOpen D) (m : ℕ) (hm : m ≤ r) (u : ℂ) (f f₂ : Q.Mx k r → E)
    (h : ∀ x ∈ Q.Glev k r 0 ∩ D, f x = f₂ x) (g : Q.Mx k r) (hg : g ∈ Q.Glev k r 0 ∩ D) :
    C3.AAop k r m hm u f g = C3.AAop k r m hm u f₂ g := by
  unfold C3.AAop
  apply Finset.sum_congr rfl
  intro c _
  split_ifs
  · rw [qminorOp_loc hD _ _ u f f₂ h g hg]
  · rfl
end Formalism.FourierDecayAlt.P.PBG
