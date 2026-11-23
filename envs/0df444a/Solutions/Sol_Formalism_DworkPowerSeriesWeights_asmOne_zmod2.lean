-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.asmOne_zmod2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:00:18.057+00:00
-- url     : https://prove2.me/submissions/3a55375f-30ee-47aa-882f-bc9da7e0dee1

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : ∀ s s' a b : ZMod 2, s.val % 2 = 0 → s'.val % 2 = 1 → s + a = s' + b →
    a + b = 1 := by
  decide
end Formalism.DworkPowerSeriesWeights
