-- Prove2me | solution 1 for DeletedPrimes.counterexample_window_of_deletion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:22:36.797496+00:00
-- url     : https://prove2.me/submissions/40a06c8f-31c8-498a-a01e-ae7482be4ad8

import Definitions.Def_DeletedPrimes_Legendre
import Definitions.Def_DeletedPrimes_Exponents
import Definitions.Def_DeletedPrimes_GoodScales
import Definitions.Def_DeletedPrimes_CompositeFloor
import Theorems.Thm_DeletedPrimes_floor_theta2
import Theorems.Thm_DeletedPrimes_counterexample_window
import Theorems.Thm_DeletedPrimes_theta2_nonneg


set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {S : Set ℕ} (F : Frame S)
    (Q : Quantization S) (L : LandauAtOne S) {θ : ℝ} (hθ8 : θ < 1 / 8) (hθ2 : theta2 S ≤ θ)
    (hθα : θ < dim S / 2) :
    (2 * θ < dim S ∧ dim S ≤ 4 * θ) ∨ 1 - (1 - Real.sqrt (1 - 8 * θ)) / 2 ≤ dim S := by
  have hθ0 : 0 ≤ θ := le_trans (theta2_nonneg S) hθ2
  have hα0 : 0 < dim S := by linarith
  have hα1 : dim S < 1 := L (by linarith)
  exact counterexample_window hα0 hα1 hθ8 hθα ((floor_theta2 hα0 hα1 F Q).trans hθ2)
end DeletedPrimes
