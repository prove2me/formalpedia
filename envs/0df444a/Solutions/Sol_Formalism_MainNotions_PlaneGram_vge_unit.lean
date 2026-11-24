-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vge_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:32:34.866362+00:00
-- url     : https://prove2.me/submissions/1921f5ec-4013-4a36-a0ec-c613bd38c348

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_zero_iff
import Theorems.Thm_Formalism_MainNotions_PlaneGram_v_unit_inv
import Theorems.Thm_Formalism_MainNotions_PlaneGram_v_unit_zpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {x : K} (h : v x = 0) :
    vge v 0 x ∧ vge v 0 x⁻¹ ∧ ∀ ε : ℤ, vge v 0 (x ^ ε) := ⟨(vge_zero_iff v _).mpr h.ge, (vge_zero_iff v _).mpr (v_unit_inv v h).ge,
    fun ε => (vge_zero_iff v _).mpr (v_unit_zpow v h ε).ge⟩
end Formalism.MainNotions.PlaneGram
