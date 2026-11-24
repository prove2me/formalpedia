-- Prove2me | solution 1 for DeletedPrimes.intervalIntegrable_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:57:47.147162+00:00
-- url     : https://prove2.me/submissions/c9f3f875-7b74-4194-8824-63cb110b1e03

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
import Theorems.Thm_DeletedPrimes_count_mono

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution (S : Set ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x => (count S x : ℝ)) volume a b := by
  have hm : Monotone (fun x => (count S x : ℝ)) := fun x y h => Nat.cast_le.mpr (count_mono S h)
  exact hm.intervalIntegrable
end DeletedPrimes
