-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.rn_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:16:01.927212+00:00
-- url     : https://prove2.me/submissions/557f03d1-17f2-4653-a8f6-575969e94f4f

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_block3_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_block3_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_wMat_ct
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_wMat_sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_hpkBlocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_block3_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_wMat_sq_assoc
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_skewOf_ct
import Theorems.Thm_Formalism_QuantumDeterminants_hpkFacts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux2
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux2
theorem _root_.solution (x : RC k j ρ) : Rn k j ρ x ∈ B.GV k (j + ρ) := by
  have hH : (Hpk k ρ)ᴴ = Hpk k ρ := (hpkFacts k ρ).1
  have hS := skewOf_ct x.2
  show (Rn k j ρ x)ᴴ * Hpk k (j + ρ) * Rn k j ρ x = Hpk k (j + ρ)
  rw [hpkBlocks k j ρ]; unfold Rn
  rw [block3_conjTranspose, block3_mul, block3_mul]
  refine block3_congr ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [Matrix.mul_assoc, wMat_ct, wMat_sq_assoc, wMat_sq, hH, hS, Matrix.conjTranspose_smul] <;> module
end Formalism.FourierDecayAlt.P.Ux2
