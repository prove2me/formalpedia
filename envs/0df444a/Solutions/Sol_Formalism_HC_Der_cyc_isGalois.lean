-- Prove2me | solution 1 for Formalism.HC.Der.cyc_isGalois
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:57:43.674845+00:00
-- url     : https://prove2.me/submissions/8df13b45-9f2a-477b-a49f-729cd1cd6e62

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycBasic

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
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits
variable (N : ℕ) [NeZero N]
namespace Formalism.HC.Der
theorem _root_.solution : IsGalois ℚ (Cond.Cyc N) := IsCyclotomicExtension.isGalois {N} ℚ _
end Formalism.HC.Der
