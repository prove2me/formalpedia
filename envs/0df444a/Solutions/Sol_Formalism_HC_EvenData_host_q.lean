-- Prove2me | solution 1 for Formalism.HC.EvenData.host_q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:34:16.084997+00:00
-- url     : https://prove2.me/submissions/d7eb70d2-5279-40a6-b146-0943d6d76de2

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
variable {q d : ℕ} (hH : HostHyp q d)
variable (hc : Nat.Coprime D.m (q * d))
variable (he : 2 ≤ D.e) (hs : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ D.m → jacobiSym (-(d : ℤ)) l = 1)
namespace Formalism.HC.EvenData
theorem _root_.solution : (D.host hH hc he hs).q = q := rfl
end Formalism.HC.EvenData
