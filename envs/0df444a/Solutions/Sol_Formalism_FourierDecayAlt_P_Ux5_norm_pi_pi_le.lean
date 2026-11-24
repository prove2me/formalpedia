-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.norm_pi_pi_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:32:47.962635+00:00
-- url     : https://prove2.me/submissions/de6787a7-daa0-45de-b488-3e6bde170bd0

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
theorem _root_.solution {α β : Type*} [Fintype α] [Fintype β] (f : α → β → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i j, ‖f i j‖ ≤ c) : ‖f‖ ≤ c :=
  (pi_norm_le_iff_of_nonneg hc).2 fun i => (pi_norm_le_iff_of_nonneg hc).2 fun j => h i j
end Formalism.FourierDecayAlt.P.Ux5
