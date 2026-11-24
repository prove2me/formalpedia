-- Prove2me | solution 1 for DeletedPrimes.kappaK_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:53:12.543485+00:00
-- url     : https://prove2.me/submissions/1716f989-a2dc-450c-b631-f47dcd5ae529

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution (α : ℝ) : kappaK 1 α = kappaOne α := by
  unfold kappaK kappaOne
  have h1 : (2 * (1 - α) + α ^ 2 / ((1 : ℕ) : ℝ)) = 1 + (1 - α) ^ 2 := by push_cast; ring
  have h2 : (1 + (1 - α) ^ 2 / ((1 : ℕ) : ℝ)) = 1 + (1 - α) ^ 2 := by push_cast; ring
  split_ifs <;> simp only [h1, h2]
end DeletedPrimes
