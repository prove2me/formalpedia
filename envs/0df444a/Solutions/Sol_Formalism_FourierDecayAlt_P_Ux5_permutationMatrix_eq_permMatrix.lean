-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.permutationMatrix_eq_permMatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:02:22.711591+00:00
-- url     : https://prove2.me/submissions/b93c3dea-5bea-4c77-8ef4-b315f168e964

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks

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
theorem _root_.solution {p : ℕ} (σ : Equiv.Perm (Fin p)) : wP σ = σ.permMatrix ℂ := by
  ext a b
  simp [wP, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
end Formalism.FourierDecayAlt.P.Ux5
