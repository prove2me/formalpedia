-- Prove2me | solution 1 for DeletedPrimes.IsMSRegular.nonneg_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:59:23.116272+00:00
-- url     : https://prove2.me/submissions/7043503c-6a8e-45c8-b8ae-911462e88ebf

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
import Theorems.Thm_DeletedPrimes_meanSq_nonneg

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
namespace IsMSRegular
theorem _root_.solution {S : Set ℕ} {θ C : ℝ}
    (h : ∀ X : ℝ, 1 ≤ X → meanSq S X ≤ C * X ^ (2 * θ)) : 0 ≤ C := by
  have := h 1 le_rfl
  rw [Real.one_rpow, mul_one] at this
  exact le_trans (meanSq_nonneg S zero_le_one) this
end IsMSRegular
end DeletedPrimes
