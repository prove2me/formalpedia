-- Prove2me | solution 1 for DeletedPrimes.sep_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:17:23.714169+00:00
-- url     : https://prove2.me/submissions/4ced0a56-c49b-42e7-a8f7-e85f70f13de0

import Mathlib
import Definitions.Def_DeletedPrimes_Rigidity

set_option autoImplicit false
open Real
open DeletedPrimes
open Classical
namespace DeletedPrimes
theorem _root_.solution {k d q m : ℤ} (hd : 0 < d) (hq : 0 < q) (h : k * q ≠ m * d) :
    1 / ((d : ℝ) * q) ≤ |(k : ℝ) / d - (m : ℝ) / q| := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hne : k * q - d * m ≠ 0 := by
    intro h'; apply h; linarith
  have h1 : (1 : ℝ) ≤ |(k : ℝ) * q - d * m| := by
    have := Int.one_le_abs hne
    exact_mod_cast this
  rw [div_sub_div _ _ hd'.ne' hq'.ne', abs_div, abs_of_pos (mul_pos hd' hq')]
  gcongr
end DeletedPrimes
