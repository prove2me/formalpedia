-- Prove2me | solution 1 for DeletedPrimes.IsRegular.nonneg_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:46:06.63448+00:00
-- url     : https://prove2.me/submissions/1faa59e1-f01e-4d38-986b-3c0af8891a7e

import Mathlib
import Definitions.Def_DeletedPrimes_Basic

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
namespace IsRegular
theorem _root_.solution {S : Set ℕ} {θ C : ℝ} (h : ∀ x : ℝ, 1 ≤ x → |err S x| ≤ C * x ^ θ) :
    0 ≤ C := by
  have := h 1 le_rfl
  rw [Real.one_rpow, mul_one] at this
  exact le_trans (abs_nonneg _) this
end IsRegular
end DeletedPrimes
