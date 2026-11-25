-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.QMinOp.opApply_append
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:57:05.495798+00:00
-- url     : https://prove2.me/submissions/f27793d4-c19b-476f-a43e-e1c445fd73ed

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatOpA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatQMinOp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.QMinOp
open Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.CutMP.QMinOp
theorem _root_.solution (Θ₁ Θ₂ : B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (g : B.Mat k r) :
    B.opApply (Θ₁ ++ Θ₂) F g = B.opApply Θ₁ F g + B.opApply Θ₂ F g := by
  unfold B.opApply
  rw [List.map_append, List.sum_append]
end Formalism.FourierDecayAlt.P.CutMP.QMinOp
