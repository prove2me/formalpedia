-- Prove2me | solution 1 for Formalism.HC.EvenData.ord_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:35:50.910338+00:00
-- url     : https://prove2.me/submissions/8c483cfd-3591-44eb-9553-49795f82ce78

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfChar
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharFrame

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
open Formalism.FrobeniusOrbits
attribute [instance] EvenData.grp
open Formalism.HC.EvenData
variable (D : EvenData)
namespace Formalism.HC.EvenData
theorem _root_.solution : D.frame.ord = Nat.card D.R := by
  show Fintype.card (Additive D.R) = Nat.card D.R
  rw [← Nat.card_eq_fintype_card]
  rfl
end Formalism.HC.EvenData
