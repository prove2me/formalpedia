-- Prove2me | solution 1 for Formalism.ZF.perron_Fy_eq_LSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:42:17.459344+00:00
-- url     : https://prove2.me/submissions/b7da325c-cce8-4a8e-85ff-e451950349e9

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology ArithmeticFunction
open scoped LSeries.notation
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution (y : ℝ) (w : ℂ) (hw : 1 < w.re) :
    Fy y w = LSeries ↗Λ w * (y : ℂ) ^ w / (w * (w - 1)) := by
  unfold Fy
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hw]
  ring
end Formalism.ZF
