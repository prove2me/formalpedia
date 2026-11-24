-- Prove2me | solution 1 for Formalism.HC.Der.kc_sqd_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:54:39.839784+00:00
-- url     : https://prove2.me/submissions/13d6c805-91ee-4beb-b3cc-3418326d1a22

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcBase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise nonZeroDivisors
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der
theorem _root_.solution : H.sqd ≠ 0 := by
  intro h
  have h1 := H.sqd_sq
  rw [h] at h1
  have hd : (H.d : H.E) = 0 := by linear_combination h1
  have hd0 : H.d = 0 := by exact_mod_cast hd
  have hc := H.QS_coprime
  rw [hd0, mul_zero, Nat.coprime_zero_right] at hc
  have ht := H.tower_dvd
  rw [hc] at ht
  have h2 : 2 ^ (φ.e + 2) ≤ 1 := Nat.le_of_dvd one_pos ht
  have h3 : 2 ^ 1 ≤ 2 ^ (φ.e + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega
end Formalism.HC.Der
