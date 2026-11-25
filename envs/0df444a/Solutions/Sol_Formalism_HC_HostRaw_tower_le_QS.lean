-- Prove2me | solution 1 for Formalism.HC.HostRaw.tower_le_QS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:04:18.206448+00:00
-- url     : https://prove2.me/submissions/676f8cc9-026e-40b9-a10c-972a0f19ecf0

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ExistsOpenNormalOrderOf
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.HostRaw
theorem _root_.solution : 2 ^ (φ.e + 2) ≤ H.QS := Nat.le_of_dvd H.QS_pos H.tower_dvd
end Formalism.HC.HostRaw
