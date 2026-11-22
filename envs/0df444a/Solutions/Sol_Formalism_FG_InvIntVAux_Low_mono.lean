-- Prove2me | solution 1 for Formalism.FG.InvIntVAux.Low.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:15:37.656916+00:00
-- url     : https://prove2.me/submissions/da6a9d60-4e71-42d4-a09f-55ee1027a29e

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
theorem _root_.solution {m k : ℕ} {x : MvPowerSeries σ K} (h : Low m x) (hk : k ≤ m) : Low k x := by
  intro d hd
  exact h d (lt_of_lt_of_le hd hk)
end Low
end Formalism.FG.InvIntVAux
