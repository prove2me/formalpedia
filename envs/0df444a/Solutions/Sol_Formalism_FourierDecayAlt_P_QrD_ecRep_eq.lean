-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.QrD.ecRep_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:24:25.849949+00:00
-- url     : https://prove2.me/submissions/5030735f-5e01-429c-86f8-7b7c4c692727

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneParameterDifferentiable
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightTypeAction
import Theorems.Thm_Formalism_FourierDecayAlt_P_QrD_dRep_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.QrD
variable {k r : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
variable [FiniteDimensional ℂ W] {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)}
namespace Formalism.FourierDecayAlt.P.QrD
theorem _root_.solution (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z)) {Z : Mx k r}
    (h1 : InLieW k r z (hpart1 (Hpk k r) Z)) (h2 : InLieW k r z (hpart2 (Hpk k r) Z)) (v : W) :
    EcRep (Hpk k r) π Z v = ecOp π Z v := by
  unfold EcRep ecOp
  rw [dRep_eq hπ hc h1, dRep_eq hπ hc h2]
  rfl
end Formalism.FourierDecayAlt.P.QrD
