-- Prove2me | solution 1 for Diaz.exp_ratMul_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:19:51.890871+00:00
-- url     : https://prove2.me/submissions/c1dbf720-b212-4396-b2af-1426ab71789a

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

open Diaz in
theorem solution {u : ℂ} (hexp : IsAlgebraic ℚ (Complex.exp u)) (a : ℚ) :
    IsAlgebraic ℚ (Complex.exp ((a : ℂ) * u)) := by
  have hq : 0 < a.den := a.pos
  have hd : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_ne_zero
  have hnum : (a : ℚ) * (a.den : ℚ) = (a.num : ℚ) := by
    rw [eq_comm, ← div_eq_iff hd]; exact Rat.num_div_den a
  have hnumC : (a : ℂ) * (a.den : ℂ) = (a.num : ℂ) := by
    exact_mod_cast congrArg (fun r : ℚ => (r : ℂ)) hnum
  have key : (Complex.exp ((a : ℂ) * u)) ^ (a.den) = (Complex.exp u) ^ (a.num) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_int_mul]
    congr 1
    rw [← mul_assoc, mul_comm ((a.den : ℂ)) ((a : ℂ)), hnumC]
  have hint : IsIntegral ℚ (Complex.exp u) := isAlgebraic_iff_isIntegral.mp hexp
  have halg : IsAlgebraic ℚ ((Complex.exp u) ^ (a.num)) := by
    rcases lt_or_ge a.num 0 with h | h
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, a.num = -(m : ℤ) := ⟨(-a.num).toNat, by omega⟩
      rw [hm, zpow_neg, zpow_natCast]
      exact IsAlgebraic.inv (isAlgebraic_iff_isIntegral.mpr (hint.pow m))
    · obtain ⟨m, hm⟩ : ∃ m : ℕ, a.num = (m : ℤ) := ⟨a.num.toNat, by omega⟩
      rw [hm, zpow_natCast]
      exact isAlgebraic_iff_isIntegral.mpr (hint.pow m)
  exact IsAlgebraic.of_pow hq (key ▸ halg)
