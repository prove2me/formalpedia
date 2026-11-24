-- Prove2me | solution 1 for Formalism.HC.unitsMap_val_modEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:34:16.897739+00:00
-- url     : https://prove2.me/submissions/a1d7dd4c-2923-4a9b-bca4-33fa1acfa05d

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
namespace Formalism.HC
theorem _root_.solution {M N : ℕ} [NeZero N] [NeZero M] (h : M ∣ N) (u : (ZMod N)ˣ) :
    (u : ZMod N).val ≡ ((ZMod.unitsMap h u : (ZMod M)ˣ) : ZMod M).val [MOD M] :=
  (unitsMap_eq_iff h u _).mp rfl
end Formalism.HC
