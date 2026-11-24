-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.rn_rset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:36:12.110092+00:00
-- url     : https://prove2.me/submissions/d1bc8b01-b719-4433-a800-ab61093fe132

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_block3_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_rset_of_blocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_rn_mem

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
theorem _root_.solution (x : RC k j ρ) : Rn k j ρ x ∈ Rset k j ρ :=
  rset_of_blocks (rn_mem x) (by ext a b; simp [b11, Rn, block3_apply]) (by ext a b; simp [b21, Rn, block3_apply])
    (by ext a b; simp [b31, Rn, block3_apply]) (by ext a b; simp [b22, Rn, block3_apply]) (by ext a b; simp [b32, Rn, block3_apply])
end Formalism.FourierDecayAlt.P.Ux2
