-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.minkowski_number_dvd_factorial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:17.184414+00:00
-- url     : https://prove2.me/submissions/b0775566-2cfc-4541-8d14-b905f65b1a93

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_prod_primepow_dvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.MinkowskiDvdFactorial := by
  intro N
  unfold minkowskiM
  apply prod_primepow_dvd _ (fun p hp => (Finset.mem_filter.1 hp).2)
  intro p hp
  have hpp : p.Prime := (Finset.mem_filter.1 hp).2
  have := Fact.mk hpp
  have hp2 : 2 ≤ p := hpp.two_le
  rw [padicValNat_dvd_iff_le (Nat.factorial_ne_zero _)]
  have hlog : Nat.log p (2 * N) < N + 2 := by
    by_cases h0 : 2 * N = 0
    · simp [h0]
    · apply Nat.log_lt_of_lt_pow h0
      have h1 : N < 2 ^ N := Nat.lt_two_pow_self
      have h2 : 2 ^ (N + 2) = 4 * 2 ^ N := by ring
      have h3 : 2 ^ (N + 2) ≤ p ^ (N + 2) := Nat.pow_le_pow_left hp2 _
      omega
  rw [padicValNat_factorial hlog, Finset.sum_Ico_eq_sum_range]
  unfold minkowskiExp
  have e : N + 2 - 1 = N + 1 := by omega
  rw [e]
  apply Finset.sum_le_sum
  intro i _
  have hpos : 0 < p ^ (1 + i) := pow_pos (by omega) _
  have hle : p ^ (1 + i) ≤ 2 * (p ^ i * (p - 1)) := by
    have h1 : p ≤ 2 * (p - 1) := by omega
    calc p ^ (1 + i) = p ^ i * p := by ring
      _ ≤ p ^ i * (2 * (p - 1)) := Nat.mul_le_mul_left _ h1
      _ = 2 * (p ^ i * (p - 1)) := by ring
  calc N / (p ^ i * (p - 1)) = (2 * N) / (2 * (p ^ i * (p - 1))) := by
        rw [Nat.mul_div_mul_left _ _ (by norm_num : 0 < 2)]
    _ ≤ (2 * N) / p ^ (1 + i) := Nat.div_le_div_left hle hpos
end Formalism.HermitianLatticeCounting.P
