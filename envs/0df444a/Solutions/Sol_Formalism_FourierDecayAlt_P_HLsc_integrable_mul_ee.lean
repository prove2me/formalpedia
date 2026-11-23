-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HLsc.integrable_mul_ee
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:53.34783+00:00
-- url     : https://prove2.me/submissions/29dde2f7-34cf-43bc-8454-9a77fba87145

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_continuous_ee
import Theorems.Thm_Formalism_FourierDecayAlt_P_Herglotz_norm_ee


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HLsc
open Real Filter Topology Finset MeasureTheory Formalism.FourierDecayAlt.P.Herglotz
variable {d : ℕ}
namespace Formalism.FourierDecayAlt.P.HLsc
theorem _root_.solution {W : (Fin d → ℝ) → ℝ} (hW : Integrable W) (σ : Fin d → ℤ) :
    Integrable (fun z => (W z : ℂ) * ee z σ) :=
  hW.ofReal.mul_bdd (c := 1) (continuous_ee σ).aestronglyMeasurable
    (Eventually.of_forall (fun z => (norm_ee z σ).le))
end Formalism.FourierDecayAlt.P.HLsc
