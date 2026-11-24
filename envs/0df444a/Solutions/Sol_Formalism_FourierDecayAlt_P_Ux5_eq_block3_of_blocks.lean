-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.eq_block3_of_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:34:41.619184+00:00
-- url     : https://prove2.me/submissions/6c96911d-9044-433b-b87a-1187fb1301a1

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_aux_statement_16

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
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux5
theorem _root_.solution (M : B.Mat k (j + ρ)) :
    M = blk3 (bk M (q1 k ρ) (q1 k ρ)) (bk M (q1 k ρ) (q2 k j)) (bk M (q1 k ρ) (q3 k ρ))
      (bk M (q2 k j) (q1 k ρ)) (bk M (q2 k j) (q2 k j)) (bk M (q2 k j) (q3 k ρ))
      (bk M (q3 k ρ) (q1 k ρ)) (bk M (q3 k ρ) (q2 k j)) (bk M (q3 k ρ) (q3 k ρ)) := by
  ext x y
  obtain ⟨x', rfl⟩ := (eB k j ρ).surjective x
  obtain ⟨y', rfl⟩ := (eB k j ρ).surjective y
  rw [aux_statement_16]
  rcases x' with ((a | a) | a) <;> rcases y' with ((b | b) | b) <;> simp [bk, q1, q2, q3]
end Formalism.FourierDecayAlt.P.Ux5
