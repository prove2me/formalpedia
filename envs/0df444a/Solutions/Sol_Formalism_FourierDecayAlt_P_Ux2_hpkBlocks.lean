-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.hpkBlocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:36:32.38408+00:00
-- url     : https://prove2.me/submissions/41584ae8-30ad-42ba-bf4a-cfa1e07cd4c8

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_eB_ll
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_eB_lr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_eB_r
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_block3_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_mat_ext_eB

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
theorem _root_.solution : HpkBlocks := by
  intro k j ρ
  apply mat_ext_eB; intro x y
  rw [block3_apply]
  rcases x with (x|x)|x <;> rcases y with (y|y)|y <;>
    (have hx := x.isLt; have hy := y.isLt
     simp [Hpk, G.wMat, Fin.ext_iff, eB_ll, eB_lr, eB_r, Fin.val_rev] <;> split_ifs <;> first | rfl | omega)
end Formalism.FourierDecayAlt.P.Ux2
