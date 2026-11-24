-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.chart_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:07:15.342802+00:00
-- url     : https://prove2.me/submissions/63c3c03f-d37c-4663-9a38-82bd48f293fe

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_dom_open
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_chart_cd

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
theorem _root_.solution (g0 : Mat k r) {Y : J k r → ℝ} (hY : Y ∈ Dom k r) : DifferentiableAt ℝ (chart g0) Y :=
  ((chart_cd g0).differentiableOn (by simp)).differentiableAt (dom_open.mem_nhds hY)
end Formalism.FourierDecayAlt.P.Ux1
