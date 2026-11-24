-- Prove2me | solution 1 for Formalism.HC.Der.Rd.div_q
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:18.185533+00:00
-- url     : https://prove2.me/submissions/9e5038d7-7c4f-4447-90ba-ad9aa711c315

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdDiff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdBound
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DvdDiscrOfInertia
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
namespace Formalism.HC.Der
open Formalism.FrobeniusOrbits
namespace Rd
variable {φ : Frame} (H : HostRaw φ)
private theorem q_mul_d_ne_zero : H.q * H.d ≠ 0 := by
  intro h0
  have h1 := H.QS_coprime
  rw [h0, Nat.coprime_zero_right] at h1
  have h2 := H.tower_dvd
  rw [h1, Nat.dvd_one] at h2
  have h3 : 2 ^ 1 ≤ 2 ^ (φ.e + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [h2] at h3
  norm_num at h3
end Rd
open Rd
variable {φ : Frame} (H : HostRaw φ)
end Formalism.HC.Der
end
end

set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits
open Formalism.HC.Der.Rd
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der.Rd
theorem _root_.solution : H.condN / H.q = H.QS * H.d := by
  show H.QS * H.q * H.d / H.q = H.QS * H.d
  rw [show H.QS * H.q * H.d = H.QS * H.d * H.q by ring]
  exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (left_ne_zero_of_mul (q_mul_d_ne_zero H)))
end Formalism.HC.Der.Rd
