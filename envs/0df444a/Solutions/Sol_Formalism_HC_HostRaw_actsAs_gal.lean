-- Prove2me | solution 1 for Formalism.HC.HostRaw.actsAs_gal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:03:06.349812+00:00
-- url     : https://prove2.me/submissions/7171da0f-5d7d-438e-ae8b-0c2beead90dd

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_AdjoinCycZeta
import Theorems.Thm_Formalism_HC_HostRaw_actsAs_of_one

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
theorem _root_.solution (j : H.E →ₐ[ℚ] Qb) (σ : H.E ≃ₐ[ℚ] H.E) :
    H.ActsAs ((j.comp (σ : H.E →ₐ[ℚ] H.E)).comp ((H.jOf j).symm : H.EQ →ₐ[ℚ] H.E)) (H.gal σ) := by
  refine actsAs_of_one j fun x => ?_
  show j (σ ((H.jOf j).symm (H.jOf j x))) = _
  rw [AlgEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
end Formalism.HC.HostRaw
