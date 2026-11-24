-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux5.EB_bk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:34:57.769583+00:00
-- url     : https://prove2.me/submissions/32115820-7e4e-4367-980e-f53bb7121c28

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetNormLe
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_entry_le_gN

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
theorem _root_.solution {k j ρ : ℕ} {ι κ : Type*} (M : B.Mat k (j + ρ)) (f : ι → Ix k j ρ) (f' : κ → Ix k j ρ) :
    EB (bk M f f') (B.gN M) :=
  fun a b => entry_le_gN M _ _
end Formalism.FourierDecayAlt.P.Ux5
