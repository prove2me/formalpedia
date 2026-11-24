-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.lowW_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:34:44.018799+00:00
-- url     : https://prove2.me/submissions/188ae3a0-1f43-4c65-989e-e721e91b5ae0

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
theorem _root_.solution {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : LW σ → ℂ) (q : LW σ) : lowW σ v q.1.1 q.1.2 = v q := by
  have h := q.2
  simp [lowW, ne_of_gt h.1, h]
end Formalism.FourierDecayAlt.P.Ux5
