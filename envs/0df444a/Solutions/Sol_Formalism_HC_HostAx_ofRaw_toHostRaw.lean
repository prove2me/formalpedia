-- Prove2me | solution 1 for Formalism.HC.HostAx.ofRaw_toHostRaw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:58:09.891829+00:00
-- url     : https://prove2.me/submissions/0b6a7c85-d08d-4b26-982c-85d77e0d724b

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycAll
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_Imports
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DvdDiscrOfInertia
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfRawToHostRaw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC
namespace Formalism.HC
namespace HostAx
theorem _root_.solution {φ : Frame} (H : HostRaw φ) : (HostAx.ofRaw H).toHostRaw = H := rfl
end HostAx
end Formalism.HC
