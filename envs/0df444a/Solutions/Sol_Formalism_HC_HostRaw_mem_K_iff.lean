-- Prove2me | solution 1 for Formalism.HC.HostRaw.mem_K_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:12:11.672491+00:00
-- url     : https://prove2.me/submissions/45ccd61e-ce72-4add-899b-baf55b504971

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_AdjoinCycZeta
import Theorems.Thm_Formalism_HC_HostRaw_map_K

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
namespace Formalism.HC.HostRaw
theorem _root_.solution (j : H.E →ₐ[ℚ] Qb) (x : H.E) : x ∈ H.K ↔ j x ∈ KQ H.d := by
  rw [← H.map_K j, IntermediateField.mem_map]
  constructor
  · intro hx; exact ⟨_, hx, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    rwa [← j.toRingHom.injective hxy]
end Formalism.HC.HostRaw
