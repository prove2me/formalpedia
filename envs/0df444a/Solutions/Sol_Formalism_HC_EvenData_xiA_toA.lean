-- Prove2me | solution 1 for Formalism.HC.EvenData.xiA_toA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:35:52.9773+00:00
-- url     : https://prove2.me/submissions/d8d19cf1-9ebe-43e4-a519-4114493b7fea

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
theorem _root_.solution (u : (ZMod D.m)ˣ) : D.xiA (D.toA u) = D.ξ u := by
  show D.p2 (D.iso (D.toA u)) = D.ξ u
  rw [iso_toA]
  rfl
end Formalism.HC.EvenData
