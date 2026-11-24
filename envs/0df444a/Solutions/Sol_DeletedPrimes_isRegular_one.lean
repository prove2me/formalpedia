-- Prove2me | solution 1 for DeletedPrimes.isRegular_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:01:05.898817+00:00
-- url     : https://prove2.me/submissions/270021d8-c087-4c47-b351-04ca7892189c

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
import Theorems.Thm_DeletedPrimes_abs_err_le

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution (S : Set ℕ) : IsRegular S 1 :=
  ⟨1 + |density S|, fun x hx => by
    rw [Real.rpow_one]; exact abs_err_le S (by linarith)⟩
end DeletedPrimes
