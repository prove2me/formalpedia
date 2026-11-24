-- Prove2me | solution 1 for Formalism.HC.HostRaw.val_unitOfCoprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:13:52.652131+00:00
-- url     : https://prove2.me/submissions/8b3f08ad-d063-4a33-86b2-237aae9dc177

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ExistsOpenNormalOrderOf
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts

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
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.HostRaw
theorem _root_.solution {p : ℕ} (h : Nat.Coprime p H.condN) :
    ((ZMod.unitOfCoprime p h : (ZMod H.condN)ˣ) : ZMod H.condN).val ≡ p [MOD H.condN] := by
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  exact Nat.mod_modEq p _
end Formalism.HC.HostRaw
