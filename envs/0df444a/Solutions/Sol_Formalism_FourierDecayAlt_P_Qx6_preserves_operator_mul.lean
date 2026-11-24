-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.preserves_operator_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:37:56.723692+00:00
-- url     : https://prove2.me/submissions/02793122-c71c-45eb-8cd7-0eea039c0f12

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution {X : Type*} [AddCommGroup X] [Module ℂ X] {R : X → X → Prop} (hR : LinRel R) {M M' N N' : OM X}
    (hM : ∀ a b, Pres2 R (M a b) (M' a b)) (hN : ∀ a b, Pres2 R (N a b) (N' a b)) (a b : Fin 2) :
    Pres2 R (oMul M N a b) (oMul M' N' a b) := by
  intro x y hxy
  simp only [oMul, Fin.sum_univ_two]
  exact hR.add (hM a 0 _ _ (hN 0 b x y hxy)) (hM a 1 _ _ (hN 1 b x y hxy))
end Formalism.FourierDecayAlt.P.Qx6
