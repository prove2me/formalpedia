-- Prove2me | solution 1 for Formalism.HC.Der.Rd.order_dvd_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:20.618724+00:00
-- url     : https://prove2.me/submissions/d4b6c298-6679-4ac9-8c4f-77d5c2b98875

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open ArithmeticFunction Finset
noncomputable section
namespace Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N]
private theorem natCast_val_zmod_eq_self (x : ZMod N) : ((x.val : ℕ) : ZMod N) = x := by
  first
  | exact ZMod.natCast_zmod_val x
  | simp
private theorem intCast_zmod_eq_zero_iff_dvd' (a : ℤ) : ((a : ZMod N) = 0) ↔ (N : ℤ) ∣ a := by
  first
  | exact CharP.intCast_eq_zero_iff (ZMod N) N a
  | exact ZMod.intCast_zmod_eq_zero_iff_dvd a N
end Formalism.HC.Der.Rd
end
end

set_option autoImplicit false
open ArithmeticFunction Finset
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N]
namespace Formalism.HC.Der.Rd
theorem _root_.solution {m : ℕ} (hm : m ∣ N) (u : ZMod N) : addOrderOf (u - 1) ∣ m ↔ u.val ≡ 1 [MOD N / m] := by
  obtain ⟨d, hd⟩ := hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact NeZero.ne N (by rw [hd, zero_mul])
  have hdm : N / m = d := by
    rw [hd, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hm0)]
  have key : m • (u - 1) = (((m : ℤ) * ((u.val : ℤ) - 1) : ℤ) : ZMod N) := by
    rw [nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, Int.cast_sub, Int.cast_natCast, Int.cast_one,
      natCast_val_zmod_eq_self]
  have hN : (N : ℤ) = (m : ℤ) * d := by exact_mod_cast hd
  rw [hdm, addOrderOf_dvd_iff_nsmul_eq_zero, key, intCast_zmod_eq_zero_iff_dvd', hN,
    mul_dvd_mul_iff_left (by exact_mod_cast hm0), Nat.modEq_iff_dvd, Nat.cast_one, dvd_sub_comm]
end Formalism.HC.Der.Rd
