-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.block3_eta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:34:51.113627+00:00
-- url     : https://prove2.me/submissions/3fab6d1b-ad6e-4eb5-8824-53ad1daceea6

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
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
variable (M : B.Mat k (j + ρ))
namespace Formalism.FourierDecayAlt.P.Ux2
theorem _root_.solution : M = blk3 (b11 M) (b12 M) (b13 M) (b21 M) (b22 M) (b23 M) (b31 M) (b32 M) (b33 M) := by
  apply mat_ext_eB; intro x y; rw [block3_apply]
  rcases x with (x|x)|x <;> rcases y with (y|y)|y <;> rfl
end Formalism.FourierDecayAlt.P.Ux2
