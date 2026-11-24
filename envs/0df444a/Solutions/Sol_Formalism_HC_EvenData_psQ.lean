-- Prove2me | solution 1 for Formalism.HC.EvenData.psQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:35:51.727632+00:00
-- url     : https://prove2.me/submissions/7f7c64d2-6ae2-41f1-89c0-30b37bc790b5

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
theorem _root_.solution : (D.host hH hc he hs).PsQ := by
  intro u
  exact D.art_ps hH u
end Formalism.HC.EvenData
