-- Prove2me | solution 1 for Formalism.FG.InvIntVAux.low_of_agree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:56.963901+00:00
-- url     : https://prove2.me/submissions/287666cb-5a76-42be-8004-897411c8be36

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
theorem _root_.solution {N : ℕ} {a b : MvPowerSeries σ K} (hab : Agree N a b) : Low N (a - b) := by
  intro d hd
  rw [map_sub, hab d hd, sub_self]
end Formalism.FG.InvIntVAux
