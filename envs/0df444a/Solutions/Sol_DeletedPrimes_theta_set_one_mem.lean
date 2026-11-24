-- Prove2me | solution 1 for DeletedPrimes.theta_set_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:04:03.258817+00:00
-- url     : https://prove2.me/submissions/e58f7242-6ba8-41dc-8e39-7e603d05616f

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
import Theorems.Thm_DeletedPrimes_isRegular_one

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution (S : Set ℕ) : (1 : ℝ) ∈ {θ : ℝ | 0 ≤ θ ∧ IsRegular S θ} :=
  ⟨zero_le_one, isRegular_one S⟩
end DeletedPrimes
