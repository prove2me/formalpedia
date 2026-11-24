-- Prove2me | solution 1 for DeletedPrimes.meanSq_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:57:53.04985+00:00
-- url     : https://prove2.me/submissions/bc65dd81-2c10-4fd4-955d-795d5229618e

import Mathlib
import Definitions.Def_DeletedPrimes_Basic

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
open Classical
namespace DeletedPrimes
theorem _root_.solution (S : Set ℕ) {X : ℝ} (hX : 0 ≤ X) : 0 ≤ meanSq S X := by
  unfold meanSq
  apply mul_nonneg (inv_nonneg.mpr hX)
  apply intervalIntegral.integral_nonneg (by linarith)
  intro x _
  positivity
end DeletedPrimes
