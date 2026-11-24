-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.chart_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:12:00.258867+00:00
-- url     : https://prove2.me/submissions/610acce0-220b-4a52-ad59-db1cab3f978f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_prj_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_kap_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_mul
import Theorems.Thm_UpperTheory_Reformulated_B_Qj14_kap_mem


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
theorem _root_.solution {g0 : Mat k r} (hg0 : g0 ∈ GV k r) {Y : J k r → ℝ} (hY : Y ∈ Dom k r) :
    chart g0 Y ∈ GV k r :=
  Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (kap_mem (prj_lie _) hY) hg0
end Formalism.FourierDecayAlt.P.Ux1
