-- Prove2me | solution 1 for DeletedPrimes.isMSRegular_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:07:08.030013+00:00
-- url     : https://prove2.me/submissions/c58710e9-9bdf-46c6-89d1-ac5fe73f74f8

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
import Theorems.Thm_DeletedPrimes_isRegular_one
import Theorems.Thm_DeletedPrimes_IsRegular_isMSRegular

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution (S : Set ℕ) : IsMSRegular S 1 :=
  (isRegular_one S).isMSRegular zero_le_one
end DeletedPrimes
