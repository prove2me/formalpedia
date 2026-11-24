-- Prove2me | solution 1 for DeletedPrimes.theta2_set_bddBelow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:57:58.495491+00:00
-- url     : https://prove2.me/submissions/52664cef-13b3-49d7-9bcb-b015632209d0

import Mathlib
import Definitions.Def_DeletedPrimes_Basic

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution (S : Set ℕ) : BddBelow {θ : ℝ | 0 ≤ θ ∧ IsMSRegular S θ} :=
  ⟨0, fun _ h => h.1⟩
end DeletedPrimes
