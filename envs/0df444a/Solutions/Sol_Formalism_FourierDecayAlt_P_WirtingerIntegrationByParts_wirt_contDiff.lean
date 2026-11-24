-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.wirt_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:05.972056+00:00
-- url     : https://prove2.me/submissions/b5af411f-63a8-4355-b13c-262514f5732f

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_wirt_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {d : ℕ}
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
theorem _root_.solution {n : ℕ} (k : Fin d) {f : (Fin d → ℂ) → V} (hf : ContDiff ℝ (n + 1 : ℕ) f) :
    ContDiff ℝ n (wirt k f) := by
  rw [wirt_eq]
  exact (wirtL V k).contDiff.comp (hf.fderiv_right (by norm_cast))
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
