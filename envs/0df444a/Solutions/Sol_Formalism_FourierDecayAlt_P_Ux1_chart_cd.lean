-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.chart_cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:45:12.1291+00:00
-- url     : https://prove2.me/submissions/952005c2-c9fc-4ebb-ad17-19fe4e82109b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_cdm_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_cdm_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_cd_prjMv
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_mono


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
theorem _root_.solution (g0 : Mat k r) : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chart g0) (Dom k r) := by
  have hP := cd_prjMv (k := k) (r := r)
  unfold chart kap
  exact cdm_mul (cdm_mul (contDiffOn_const.add (hP.mono (Set.subset_univ _)))
    (cdm_inv (contDiffOn_const.sub (hP.mono (Set.subset_univ _))) fun Y hY => hY)) contDiffOn_const
end Formalism.FourierDecayAlt.P.Ux1
