-- Prove2me | solution 1 for Formalism.FG.InvIntVAux.Low.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:16:27.836019+00:00
-- url     : https://prove2.me/submissions/9243410e-cfbc-4827-a853-7cb1c452d5e7

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_InvIntV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.InvIntVAux
open Formalism.G Formalism.G.LogCR
variable {K : Type u} [NormedField K]
variable {σ : Type*}
namespace Formalism.FG.InvIntVAux
namespace Low
theorem _root_.solution {m : ℕ} {x y : MvPowerSeries σ K} (hx : Low m x) (hy : Low m y) :
    Low m (x + y) := by
  intro d hd
  rw [map_add, hx d hd, hy d hd, add_zero]
end Low
end Formalism.FG.InvIntVAux
