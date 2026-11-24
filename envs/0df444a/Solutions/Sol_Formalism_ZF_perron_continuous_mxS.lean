-- Prove2me | solution 1 for Formalism.ZF.perron_continuous_mxS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:43:07.419044+00:00
-- url     : https://prove2.me/submissions/867da200-095b-41e8-a440-e23815ca0fea

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
theorem _root_.solution (n : ℕ) : Continuous (Formalism.mxS n) := by
  show Continuous (fun x : ℝ => max (x / n - 1) 0)
  exact ((continuous_id.div_const _).sub continuous_const).max continuous_const
end Formalism.ZF
