-- Prove2me | solution 1 for Formalism.HC.HostRaw.EQ_le_cycQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:10:19.654169+00:00
-- url     : https://prove2.me/submissions/4c41bf9c-c27d-427c-a613-f9a893a12526

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_AdjoinCycZeta
import Theorems.Thm_Formalism_HC_HostRaw_adjoin_cycZeta
import Theorems.Thm_Formalism_L2_Host_cycQ_eq


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
theorem _root_.solution : H.EQ ≤ cycQ H.condN := by
  let κ : Cond.Cyc H.condN →ₐ[ℚ] Qb := IsAlgClosed.lift
  have hz : IsPrimitiveRoot (κ H.cycZeta) H.condN := H.cycZeta_prim.map_of_injective κ.toRingHom.injective
  have hκ : κ.fieldRange = cycQ H.condN := by
    rw [AlgHom.fieldRange_eq_map, ← H.adjoin_cycZeta, adjoin_map, Set.image_singleton, cycQ_eq hz]
  rw [← H.range_eq (κ.comp H.cycEmb), ← hκ]
  rintro _ ⟨x, rfl⟩
  exact ⟨H.cycEmb x, rfl⟩
end Formalism.HC.HostRaw
