-- Prove2me | solution 1 for DeletedPrimes.theta2_set_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:08:29.22499+00:00
-- url     : https://prove2.me/submissions/1b7e74ee-be78-44ae-9d33-87974f64e821

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
import Theorems.Thm_DeletedPrimes_isMSRegular_one

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution (S : Set ℕ) : (1 : ℝ) ∈ {θ : ℝ | 0 ≤ θ ∧ IsMSRegular S θ} :=
  ⟨zero_le_one, isMSRegular_one S⟩
end DeletedPrimes
