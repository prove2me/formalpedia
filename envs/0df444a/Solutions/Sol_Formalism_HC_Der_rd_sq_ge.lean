-- Prove2me | solution 1 for Formalism.HC.Der.rd_sq_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:09.556532+00:00
-- url     : https://prove2.me/submissions/3d9d0d54-bd20-493a-8df9-1147bc4e3ddc

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdDiff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdBound
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DvdDiscrOfInertia
import Theorems.Thm_Formalism_HC_Der_Rd_log_rd_eq
import Theorems.Thm_Formalism_HC_Der_Rd_rd_pos
import Theorems.Thm_Formalism_HC_Der_Rd_log_index_le
import Theorems.Thm_Formalism_HC_Frame_natCard_GG


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
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits
open Rd
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der
theorem _root_.solution (C : HostCore H) : (4 * φ.ord : ℝ) ≤ H.rd ^ 2 := by
  have h1 := log_index_le H.art.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr C.art_surj, Subgroup.card_top, φ.natCard_GG] at h1
  have h0 : (0 : ℝ) < φ.ord := by exact_mod_cast φ.ord_pos
  rw [← Real.log_le_log_iff (by positivity) (pow_pos (rd_pos H) 2), Real.log_pow, log_rd_eq]
  exact_mod_cast h1
end Formalism.HC.Der
