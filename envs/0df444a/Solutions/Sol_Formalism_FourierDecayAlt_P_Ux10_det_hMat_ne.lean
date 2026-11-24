-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:55:13.90817+00:00
-- url     : https://prove2.me/submissions/ae36fe1b-9bda-4079-b948-f07ec2f2b79b

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyTransformPreservesForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_permutationMatrix_eq_permMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_permutationMatrix_eq_permMatrix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux10
namespace Formalism.FourierDecayAlt.P.Ux10
theorem _root_.solution {p : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0) :
    (hMat σ d).det ≠ 0 := by
  unfold hMat
  rw [Matrix.det_mul, permutationMatrix_eq_permMatrix, Matrix.det_permutation, Matrix.det_diagonal]
  refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.mpr fun i _ => hd i)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
end Formalism.FourierDecayAlt.P.Ux10
