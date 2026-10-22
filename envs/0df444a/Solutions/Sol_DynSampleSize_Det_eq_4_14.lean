-- Prove2me | solution 1 for DynSampleSize.Det.eq_4_14
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:30:27.921995+00:00
-- url     : https://prove2.me/submissions/6a60ff64-abe4-401d-bddd-07650dd537dd

import Mathlib
import Definitions.Def_DynSampleSize_Det_Setting
set_option autoImplicit false
open Filter Topology

theorem solution {m : ℕ} (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (g v : EuclideanSpace ℝ (Fin m)) (h48 : ‖g - v‖ ≤ θ * ‖g‖) :
    (1 - θ) * ‖g‖ ^ 2 ≤ inner ℝ v g := by
  have h1 : inner ℝ (g - v) g ≤ ‖g - v‖ * ‖g‖ := real_inner_le_norm _ _
  have h2 : inner ℝ (g - v) g = ‖g‖ ^ 2 - inner ℝ v g := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq]
  have h3 : ‖g - v‖ * ‖g‖ ≤ θ * ‖g‖ * ‖g‖ :=
    mul_le_mul_of_nonneg_right h48 (norm_nonneg _)
  nlinarith [h1, h2, h3]
