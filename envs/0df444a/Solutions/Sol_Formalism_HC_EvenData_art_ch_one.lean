-- Prove2me | solution 1 for Formalism.HC.EvenData.art_ch_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:34:12.363113+00:00
-- url     : https://prove2.me/submissions/29e9ba7d-df62-4165-8c67-910340c5de62

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
namespace Formalism.HC.EvenData
theorem _root_.solution (u : (ZMod (D.m * q * d))ˣ) {y : ℕ} (hu : (u : ZMod (D.m * q * d)).val ≡ y [MOD d])
    (hy : jacobiSym (y : ℤ) d = 1) : (D.art hH u).1.2 = 1 := by
  have h1 := D.art_ch hH u
  have h2 : jacobiSym (((u : ZMod (D.m * q * d)).val : ℕ) : ℤ) d = jacobiSym (y : ℤ) d := by
    rw [jacobiSym.mod_left, jacobiSym.mod_left (y : ℤ)]
    congr 1
    exact_mod_cast (hu : _ % d = _ % d)
  rw [h2, hy] at h1
  exact Units.ext h1
end Formalism.HC.EvenData
