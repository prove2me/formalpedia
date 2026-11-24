-- Prove2me | solution 1 for Formalism.HC.HostRaw.artin_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:20:41.291477+00:00
-- url     : https://prove2.me/submissions/f61f6109-4ce2-4ee0-af2b-0f20ac4b727a

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_AdjoinCycZeta
import Theorems.Thm_Formalism_HC_HostRaw_artin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IntermediateField NumberField
open Formalism Formalism.HC Formalism.HC.HostRaw
open Formalism.FrobeniusOrbits Formalism.L2.Host
variable {φ : Frame} (H : HostRaw φ)
variable {H}
variable (H)
namespace Formalism.HC.HostRaw
theorem _root_.solution (s : Qb ≃ₐ[ℚ] Qb) (u : (ZMod H.condN)ˣ) (hs : ∀ z ∈ mus H.condN, s z = z ^ (u : ZMod H.condN).val)
    (j : H.E →ₐ[ℚ] Qb) (x : H.E) : s (j x) = j (H.gal.symm (H.art u) x) := H.artin s u hs j x
end Formalism.HC.HostRaw
