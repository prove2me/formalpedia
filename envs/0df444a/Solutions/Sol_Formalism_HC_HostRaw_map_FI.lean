-- Prove2me | solution 1 for Formalism.HC.HostRaw.map_FI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:42:38.006222+00:00
-- url     : https://prove2.me/submissions/c86ce98d-2df6-4917-9175-6768a1e91d33

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_AdjoinCycZeta
import Theorems.Thm_Formalism_HC_HostRaw_aut_mem_F

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
theorem _root_.solution (j : H.E →ₐ[ℚ] Qb) : H.FI.map j = H.FQ := by
  refine le_antisymm (le_iSup (fun j : H.E →ₐ[ℚ] Qb => H.FI.map j) j) (iSup_le fun j' => ?_)
  obtain ⟨σ, hσ⟩ := H.exists_aut j j'
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨σ x, H.aut_mem_F σ hx, (hσ x).symm⟩
end Formalism.HC.HostRaw
