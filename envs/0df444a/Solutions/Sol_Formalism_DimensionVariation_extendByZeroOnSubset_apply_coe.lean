-- Prove2me | solution 1 for Formalism.DimensionVariation.extendByZeroOnSubset_apply_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:47:47.407789+00:00
-- url     : https://prove2.me/submissions/5b2a8bd7-3ae5-43bd-9961-ce643a6d8d83

import Definitions.Def_Formalism_ThetaSupremumBounds_StatementB
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_DominanceMono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.DimensionVariation
namespace Formalism.DimensionVariation
theorem _root_.solution {r : ℕ} (f : Fin r → ℝ) (i : Fin r) : ext0 f (i : ℕ) = f i := by
  simp [ext0, i.2]
end Formalism.DimensionVariation
