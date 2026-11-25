-- Prove2me | solution 1 for Formalism.FG.FormalGroupLawMap.map_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:33:00.803328+00:00
-- url     : https://prove2.me/submissions/b7d935f8-c973-41ba-82e5-d6b4c1b9264a

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftFE
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_WittTeichmullerRoot
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_GroupV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftAsm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FG Formalism.FG.FormalGroupLawMap
open MvPowerSeries
variable {R S : Type*} [CommRing R] [CommRing S]
namespace Formalism.FG.FormalGroupLawMap
theorem _root_.solution {σ : Type*} (h : R →+* S) (hh : Function.Injective h) {f g : MvPowerSeries σ R}
    (e : map h f = map h g) : f = g := by
  ext n
  have := congrArg (coeff n) e
  simp only [coeff_map] at this
  exact hh this
end Formalism.FG.FormalGroupLawMap
