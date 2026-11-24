-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.beta_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:56:37.175305+00:00
-- url     : https://prove2.me/submissions/3b8e2e28-4c06-4d15-a9b0-2a2c3cb81712

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_wMat_mul_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_wMat_ct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux5
namespace Formalism.FourierDecayAlt.P.Ux5
theorem _root_.solution {N j : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (c : Matrix (Fin N) (Fin j) ℂ)
    (S : Matrix (Fin j) (Fin j) ℂ) (hH : Hᴴ = H) (hS : Sᴴ = -S) :
    G.wMat j * ((-(1 / 2 : ℂ)) • (cᴴ * H * c) + S) =
      -(G.wMat j * (G.wMat j * ((-(1 / 2 : ℂ)) • (cᴴ * H * c) + S) - (-(G.wMat j * cᴴ * H)) * c)ᴴ *
        G.wMat j) := by
  set w := G.wMat j
  set X := cᴴ * H * c with hX
  have hXc : Xᴴ = X := by
    rw [hX, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH, Matrix.mul_assoc]
  have h1 : (-(w * cᴴ * H)) * c = -(w * X) := by
    rw [hX, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  have h2 : w * ((-(1 / 2 : ℂ)) • X + S) - -(w * X) = w * ((1 / 2 : ℂ) • X + S) := by
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul]
    module
  rw [h1, h2, conjTranspose_mul, conjTranspose_add, conjTranspose_smul, hXc, hS, wMat_ct,
    Matrix.mul_assoc, Matrix.mul_assoc, wMat_mul_self, Matrix.mul_one]
  have h3 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [h3, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_neg]
  module
end Formalism.FourierDecayAlt.P.Ux5
