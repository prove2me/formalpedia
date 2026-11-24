-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.expandL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:57:18.758627+00:00
-- url     : https://prove2.me/submissions/3c03f924-934d-4a71-8ab2-0aa1eeb56cc0

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_prj_of_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_prj_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_Mv_co
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_Mv_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_prj_Eb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux1
theorem _root_.solution {Z : Mat k r} (hZ : inLie k r Z) : Z = ∑ i, kc i Z • Lt i := by
  conv_lhs => rw [← prj_of_lie hZ, ← Mv_co Z, Mv_sum, prj_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [prj_Eb, smul_smul]
  rfl
end Formalism.FourierDecayAlt.P.Ux1
