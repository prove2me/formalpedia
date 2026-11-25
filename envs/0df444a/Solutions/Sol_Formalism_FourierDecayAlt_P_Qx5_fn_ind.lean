-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.fn_ind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:09:30.086135+00:00
-- url     : https://prove2.me/submissions/3f17b1da-c496-4ab8-b8f2-10d3b960b896

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
namespace Formalism.FourierDecayAlt.P.Qx5
theorem _root_.solution (j : Fin 6) {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') :
    (fun c g => (DomR k r z z').indicator (fun x => fnVal k r z z' j x.2 • Φ x.1 x.2) (c, g)) =
      fun c g => fnVal k r z z' j g • Φ c g := by
  funext c g
  by_cases hx : (c, g) ∈ DomR k r z z'
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, hΦ.1 (c, g) hx, smul_zero]
end Formalism.FourierDecayAlt.P.Qx5
