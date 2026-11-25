-- Prove2me | solution 1 for Formalism.IncomingBounds.tpjet_jetAt0_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:34:18.344855+00:00
-- url     : https://prove2.me/submissions/7e0a73e5-2de3-4da2-8566-854648e7b84e

import Definitions.Def_Formalism_IncomingBounds_DefsThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPJet

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
open Formalism Formalism.IncomingBounds
variable {C : Type} [Field C]
namespace Formalism.IncomingBounds
theorem _root_.solution {σ : Type} (G : MvPowerSeries σ C) :
    jetAt0 (0 : MvPolynomial σ C) G = 0 := by
  unfold jetAt0
  simp
end Formalism.IncomingBounds
