-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.cd_Mv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:35:15.586319+00:00
-- url     : https://prove2.me/submissions/1064ea22-71ab-4b7d-98c6-ab8d6ec39cef

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_cdm_iff

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
theorem _root_.solution : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Mv : (J k r → ℝ) → Mat k r) := by
  rw [← contDiffOn_univ, cdm_iff]
  intro p q
  simp only [Mv, Matrix.of_apply]
  exact ((Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (p, q, false))).add
    ((Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ (p, q, true))).mul contDiff_const)).contDiffOn
end Formalism.FourierDecayAlt.P.Ux1
