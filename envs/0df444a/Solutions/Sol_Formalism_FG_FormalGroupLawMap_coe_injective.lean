-- Prove2me | solution 1 for Formalism.FG.FormalGroupLawMap.coe_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:07:19.175999+00:00
-- url     : https://prove2.me/submissions/a477794e-60ca-40ca-83ea-1f67b1f88f34

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
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Formalism.FG.FormalGroupLawMap
theorem _root_.solution (l : ℕ) [Fact l.Prime] : Function.Injective (PadicInt.Coe.ringHom (p := l)) :=
  fun _ _ e => Subtype.ext e
end Formalism.FG.FormalGroupLawMap
