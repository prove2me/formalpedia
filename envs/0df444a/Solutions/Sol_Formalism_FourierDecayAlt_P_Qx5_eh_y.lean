-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx5.eh_y
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:59:22.486494+00:00
-- url     : https://prove2.me/submissions/a6f6749a-4b80-490b-a7ed-0a0af7488048

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_eh_inv
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Qx5_single_mulVec__ad7365b648dd
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_bvec_posL

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
open Qx2
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
variable (z z' : Fin (2 * r + k + 1) → ℂ)
namespace Formalism.FourierDecayAlt.P.Qx5
theorem _root_.solution (a b c : Fin (mdim k r i)) (g : Mx k r) :
    EH k r (posL k r i a) (posL k r i b) (fun g => yv k r z i g c) g = if a = c then -yv k r z i g b else 0 := by
  have h := eh_inv (LinearMap.proj (posL k r i c)) (fvec k r z i) g (posL k r i a) (posL k r i b)
  refine Eq.trans h ?_
  rw [single_mulVec', LinearMap.proj_apply, Pi.smul_apply, bvec_posL, smul_eq_mul]
  by_cases hac : a = c
  · rw [if_pos hac, if_pos hac.symm, mul_one]; rfl
  · rw [if_neg hac, if_neg (Ne.symm hac), mul_zero, neg_zero]
end Formalism.FourierDecayAlt.P.Qx5
