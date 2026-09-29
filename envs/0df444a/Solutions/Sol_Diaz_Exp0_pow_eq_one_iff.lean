-- Prove2me | solution 1 for Diaz.Exp0_pow_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T08:24:09.183108+00:00
-- url     : https://prove2.me/submissions/653d0ee7-26b7-44b7-95cc-9b857f440eec

import Mathlib
import Definitions.Def_Diaz_Exponential

namespace Diaz

section
open ComplexConjugate

theorem two_rpow_eq_one_iff (r : ℝ) : (2 : ℝ) ^ r = 1 ↔ r = 0 := by
  rw [Real.rpow_def_of_pos (by norm_num), Real.exp_eq_one_iff]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h (by positivity)
    · exact h
  · rintro rfl; ring
end

section
open ComplexConjugate

/-- **The kernel of this `Exp₀` is the divisible line `a + b = 0`.**

A property of this choice, not of the model — see the caveat in the file
header, where a variant with a lattice kernel is given. -/
theorem Exp0_eq_one_iff (x : ℚ × ℚ) : Exp0 x = 1 ↔ x.1 + x.2 = 0 := by
  rw [Exp0, two_rpow_eq_one_iff]
  exact_mod_cast Iff.rfl
end

end Diaz

section
open ComplexConjugate

open Diaz in
theorem solution (x : ℚ × ℚ) {n : ℕ} (hn : n ≠ 0) :
    Exp0 x ^ n = 1 ↔ Exp0 x = 1 := by
  constructor
  · intro h
    have hx : Exp0 x ^ n = (2 : ℝ) ^ (((x.1 + x.2) * n : ℚ) : ℝ) := by
      rw [Exp0, ← Real.rpow_natCast ((2:ℝ) ^ (((x.1 + x.2 : ℚ)) : ℝ)) n,
        ← Real.rpow_mul (by norm_num)]
      push_cast
      ring_nf
    rw [hx, two_rpow_eq_one_iff] at h
    rw [Exp0_eq_one_iff]
    have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have : ((x.1 + x.2) * n : ℚ) = 0 := by exact_mod_cast h
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · exact absurd h' hn'
  · intro h; rw [h, one_pow]
end
