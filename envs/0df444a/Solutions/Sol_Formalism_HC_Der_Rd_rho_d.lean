-- Prove2me | solution 1 for Formalism.HC.Der.Rd.rho_d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:30:10.965066+00:00
-- url     : https://prove2.me/submissions/4a8b7a15-0455-4b30-b0e8-b53ed9fdeed5

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdDiff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdBound
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DvdDiscrOfInertia
import Theorems.Thm_Formalism_HC_Der_Rd_div_d
import Theorems.Thm_Formalism_HC_Der_Rd_mem_KK
import Theorems.Thm_Formalism_HC_Der_Rd_rho_le_half


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
open Formalism.HC.Der.Rd
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der.Rd
theorem _root_.solution : rho H.art.ker (H.condN / H.d) ≤ 1 / 2 := by
  rw [div_d]
  refine rho_le_half _ (dvd_mul_right _ _) fun u hu v hv h1 h2 => ?_
  rw [MonoidHom.mem_ker] at h1 h2 ⊢
  rw [map_mul, (H.art_d u (mem_KK.mp hu)).resolve_left h1, (H.art_d v (mem_KK.mp hv)).resolve_left h2]
  exact Prod.ext (show ((1, -1) : G0) * (1, -1) = 1 by decide) (mul_one _)
end Formalism.HC.Der.Rd
