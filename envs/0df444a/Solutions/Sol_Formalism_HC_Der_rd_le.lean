-- Prove2me | solution 1 for Formalism.HC.Der.rd_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:09.398441+00:00
-- url     : https://prove2.me/submissions/25754f60-df1c-41e7-a3c4-a105290fed6d

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdDiff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdBound
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DvdDiscrOfInertia
import Theorems.Thm_Formalism_HC_Der_Rd_log_rd_eq
import Theorems.Thm_Formalism_HC_Der_Rd_rd_pos
import Theorems.Thm_Formalism_HC_Der_Rd_q_ne_d
import Theorems.Thm_Formalism_HC_Der_Rd_rho_d
import Theorems.Thm_Formalism_HC_Der_Rd_rho_q
import Theorems.Thm_Formalism_HC_Der_Rd_SS_le


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
theorem _root_.solution : H.rd ≤ (H.QS : ℝ) / 2 * Real.sqrt ((H.q : ℝ) * H.d) := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
  have hq : (0 : ℝ) < H.q := by exact_mod_cast H.hyp.1.pos
  have hS : (0 : ℝ) < H.QS := by exact_mod_cast H.QS_pos
  have h1 := SS_le H.art.ker ((dvd_pow_self 2 (by omega)).trans (two_dvd H)) H.hyp.1 H.hyp.2.1
    ((dvd_mul_left _ _).mul_right _) (dvd_mul_left _ _) (by have := H.hyp.2.2.1; omega)
    (by have := H.hyp.2.2.2.1; omega) (q_ne_d H) (rho_q H) (rho_d H)
  have hN : Real.log (H.condN : ℝ) = Real.log H.QS + Real.log H.q + Real.log H.d := by
    rw [Nat.cast_mul, Nat.cast_mul, Real.log_mul (by positivity) hd.ne', Real.log_mul hS.ne' hq.ne']
  rw [hN] at h1
  rw [← Real.log_le_log_iff (rd_pos H) (by positivity), log_rd_eq, Real.log_mul (by positivity) (by positivity),
    Real.log_div hS.ne' (by norm_num), Real.log_sqrt (by positivity), Real.log_mul hq.ne' hd.ne']
  linarith
end Formalism.HC.Der
