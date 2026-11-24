-- Prove2me | solution 1 for DeletedPrimes.aestronglyMeasurable_err
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:57:52.469806+00:00
-- url     : https://prove2.me/submissions/45d781b8-ea37-46d2-b0be-06338493107f

import Mathlib
import Definitions.Def_DeletedPrimes_Basic
import Theorems.Thm_DeletedPrimes_count_mono

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution (S : Set ℕ) : AEStronglyMeasurable (err S) volume := by
  have hm : Monotone (fun x => (count S x : ℝ)) := fun x y h => Nat.cast_le.mpr (count_mono S h)
  have h1 : Measurable (fun x => (count S x : ℝ)) := hm.measurable
  have h2 : Measurable (fun x : ℝ => density S * x) := (continuous_const.mul continuous_id).measurable
  exact (h1.sub h2).aestronglyMeasurable
end DeletedPrimes
