-- Prove2me | solution 1 for Formalism.HC.CharData.toHostRaw_QS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:58:57.252885+00:00
-- url     : https://prove2.me/submissions/be361aaf-94e8-4c09-baea-b68398ba4415

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
theorem _root_.solution : D.toHostRaw.QS = D.QS := rfl
end Formalism.HC.CharData
