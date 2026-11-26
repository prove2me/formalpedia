-- Prove2me | solution 1 for FirstPassageLinearTransport.orbit_lower_by_halving
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:53:34.323472+00:00
-- url     : https://prove2.me/submissions/b8e5a548-42f7-4067-a750-cc991572d884

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
import Theorems.Thm_FirstPassageLinearTransport_pure_multiplicative_le_orbit


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (n j : ℕ) :
    (n : ℝ) / (2 : ℝ) ^ j ≤ (orbit j n : ℝ) := by
  have hthree : (1 : ℝ) ≤ (3 : ℝ) ^ oddCount n j :=
    one_le_pow₀ (by norm_num)
  calc
    (n : ℝ) / (2 : ℝ) ^ j =
        (1 / (2 : ℝ) ^ j) * (n : ℝ) := by ring
    _ ≤ ((3 : ℝ) ^ oddCount n j / (2 : ℝ) ^ j) * (n : ℝ) := by
      gcongr
    _ ≤ (orbit j n : ℝ) := pure_multiplicative_le_orbit n j
end FirstPassageLinearTransport
