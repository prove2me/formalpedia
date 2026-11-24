-- Prove2me | solution 1 for DeletedPrimes.sep_of_pair_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:17:26.810805+00:00
-- url     : https://prove2.me/submissions/75d08074-3cd2-415a-91aa-19ee5c98b566

import Mathlib
import Definitions.Def_DeletedPrimes_Rigidity

set_option autoImplicit false
open Real
open DeletedPrimes
open Classical
namespace DeletedPrimes
theorem _root_.solution {q q' : ℕ} {m m' : ℤ} (hq : 0 < q) (hq' : 0 < q') (hm : m = 1 ∨ m = -1)
    (hm' : m' = 1 ∨ m' = -1) (hne : (q, m) ≠ (q', m')) :
    1 / ((q : ℝ) * q') ≤ |(m : ℝ) / q - (m' : ℝ) / q'| := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hqr' : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hne' : m * (q' : ℤ) - (q : ℤ) * m' ≠ 0 := by
    have hqq : q ≠ q' ∨ m ≠ m' := by
      by_contra hc
      push Not at hc
      exact hne (by rw [hc.1, hc.2])
    rcases hm with rfl | rfl <;> rcases hm' with rfl | rfl <;> omega
  have h1 : (1 : ℝ) ≤ |(m : ℝ) * q' - q * m'| := by
    have := Int.one_le_abs hne'
    exact_mod_cast this
  rw [div_sub_div _ _ hqr.ne' hqr'.ne', abs_div, abs_of_pos (mul_pos hqr hqr')]
  gcongr
end DeletedPrimes
