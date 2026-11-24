-- Prove2me | solution 1 for Formalism.HC.HostRaw.FQ_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:04:49.553864+00:00
-- url     : https://prove2.me/submissions/72807169-c3b1-4355-bf08-56c4d93a9e86

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_AdjoinCycZeta
import Theorems.Thm_Formalism_HC_HostRaw_map_FI

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
theorem _root_.solution (τ : Qb →+* ℂ) {y : Qb} (hy : y ∈ H.FQ) : starRingEnd ℂ (τ y) = τ y := by
  obtain ⟨j⟩ := H.nonempty_emb
  rw [← H.map_FI j] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact hx (τ.comp j.toRingHom)
end Formalism.HC.HostRaw
