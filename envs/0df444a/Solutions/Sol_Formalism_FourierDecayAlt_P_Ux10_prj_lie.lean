-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux10.prj_lie
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:34:46.693027+00:00
-- url     : https://prove2.me/submissions/13514c75-8124-4087-86c4-26418eed7c67

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_hpk_herm
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Ux10_hpk_sq__fc470001abcf
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_hpk_herm


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
open MeasureTheory Filter Topology
open Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux10
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux10
theorem _root_.solution (Z : Mat k r) : inLie k r (prj Z) := by
  unfold inLie prj
  have hH := (hpk_herm (k := k) (r := r))
  have hHH := (hpk_sq' (k := k) (r := r))
  rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hH,
    conjTranspose_conjTranspose]
  have h1 : Hpk k r * (Z * Hpk k r) * Hpk k r = Hpk k r * Z := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hHH, Matrix.mul_one]
  have h2 : Hpk k r * (Hpk k r * Zᴴ * Hpk k r) = Zᴴ * Hpk k r := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hHH, Matrix.one_mul]
  have hs : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [hs, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, h1, h2, ← smul_add]
  simp
end Formalism.FourierDecayAlt.P.Ux10
