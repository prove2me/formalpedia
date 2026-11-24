-- Prove2me | solution 1 for DeletedPrimes.abs_err_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:58:53.046857+00:00
-- url     : https://prove2.me/submissions/92b10f68-b443-4ddc-ab32-7c1ce44f3291

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
import Theorems.Thm_DeletedPrimes_count_le

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution (S : Set ℕ) {x : ℝ} (hx : 0 ≤ x) : |err S x| ≤ (1 + |density S|) * x := by
  unfold err
  have h0 : (0 : ℝ) ≤ count S x := Nat.cast_nonneg _
  have h1 := count_le S hx
  calc |(count S x : ℝ) - density S * x| ≤ |(count S x : ℝ)| + |density S * x| := abs_sub _ _
    _ = (count S x : ℝ) + |density S| * x := by rw [abs_of_nonneg h0, abs_mul, abs_of_nonneg hx]
    _ ≤ x + |density S| * x := by linarith
    _ = (1 + |density S|) * x := by ring
end DeletedPrimes
