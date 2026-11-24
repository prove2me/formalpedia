-- Prove2me | solution 1 for DeletedPrimes.kappaOne_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:16:14.500035+00:00
-- url     : https://prove2.me/submissions/812df9a3-1894-46d0-b90e-decbc12cc7bd

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution (α : ℝ) : α * kappaOne α / 2 = α * (1 - α) / (2 * (1 + (1 - α) ^ 2)) := by
  unfold kappaOne
  have : (0 : ℝ) < 1 + (1 - α) ^ 2 := by positivity
  field_simp
end DeletedPrimes
