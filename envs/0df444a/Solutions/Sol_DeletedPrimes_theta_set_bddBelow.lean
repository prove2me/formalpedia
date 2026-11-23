-- Prove2me | solution 1 for DeletedPrimes.theta_set_bddBelow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:49:39.509796+00:00
-- url     : https://prove2.me/submissions/50cfa360-1240-460b-a830-2fbf8e265ea8

import Mathlib
import Definitions.Def_DeletedPrimes_Basic

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution (S : Set ℕ) : BddBelow {θ : ℝ | 0 ≤ θ ∧ IsRegular S θ} :=
  ⟨0, fun _ h => h.1⟩
end DeletedPrimes
