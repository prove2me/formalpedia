-- Prove2me | solution 1 for DeletedPrimes.theta2_le_of_isMSRegular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:59:08.425038+00:00
-- url     : https://prove2.me/submissions/23bb827c-81dd-4d1c-85fc-f66dfe264b8d

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
import Theorems.Thm_DeletedPrimes_theta2_set_bddBelow

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution {S : Set ℕ} {θ : ℝ} (h0 : 0 ≤ θ) (h : IsMSRegular S θ) :
    theta2 S ≤ θ :=
  csInf_le (theta2_set_bddBelow S) ⟨h0, h⟩
end DeletedPrimes
