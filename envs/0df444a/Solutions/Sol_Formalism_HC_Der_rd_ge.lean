-- Prove2me | solution 1 for Formalism.HC.Der.rd_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:09.014274+00:00
-- url     : https://prove2.me/submissions/68e993ec-79bd-423b-b3cc-43a119ae62da

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdDiff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdBound
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DvdDiscrOfInertia
import Theorems.Thm_Formalism_HC_Der_Rd_hcl_eq_one
import Theorems.Thm_Formalism_HC_Der_Rd_log_rd_eq
import Theorems.Thm_Formalism_HC_Der_Rd_rd_pos
import Theorems.Thm_Formalism_HC_Der_Rd_hH_art
import Theorems.Thm_Formalism_HC_Der_Rd_div_d
import Theorems.Thm_Formalism_HC_Der_Rd_exists_d
import Theorems.Thm_Formalism_HC_Der_Rd_half_le_rho
import Theorems.Thm_Formalism_HC_Der_Rd_le_SS


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
theorem _root_.solution (C : HostCore H) : (2 : ℝ) ^ ((φ.e : ℝ) + 1 - (2 : ℝ) ^ (-(φ.e : ℝ))) * Real.sqrt H.d ≤ H.rd := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
  have h1 := le_SS H.art.ker (two_dvd H) H.hyp.2.1 (dvd_mul_left _ _) (by have := H.hyp.2.2.2.1; omega)
    (fun u hu => hcl_eq_one (by rw [← hH_art, MonoidHom.mem_ker.mp hu]; exact map_one _))
    (by rw [div_d]; exact half_le_rho _ (dvd_mul_right _ _) (exists_d H C))
  rw [← Real.log_le_log_iff (by positivity) (rd_pos H), log_rd_eq, Real.log_mul (by positivity) (by positivity),
    Real.log_rpow (by norm_num), Real.log_sqrt hd.le, Real.rpow_neg (by norm_num), Real.rpow_natCast, ← one_div]
  exact h1
end Formalism.HC.Der
