-- Prove2me | solution 1 for Formalism.HC.CharData.toHostRaw_art
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:59:05.052794+00:00
-- url     : https://prove2.me/submissions/4b770d5c-a40b-4642-a7fc-bfa72d1ffefa

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.CharData
variable {φ : Frame} (D : CharData φ)
namespace Formalism.HC.CharData
theorem _root_.solution : D.toHostRaw.art = D.art := rfl
end Formalism.HC.CharData
