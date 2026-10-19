-- Prove2me | solution 1 for CohnElkies.poissonLogisticDensity_le_pi_exp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/e7bd2c8a-27cf-48d6-99bd-d01998af1731

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripNormalizedPoissonExtension_one
import Theorems.Thm_CohnElkies_stripNormalizedPoissonExtension_le_majorant
import Theorems.Thm_CohnElkies_poissonLogisticDensity_eq_limitingStripPoissonDensity

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution (u : ℝ) :
    poissonLogisticDensity u ≤
      Real.pi * Real.exp (-Real.pi * |u|) := by
  have hbound :=
    stripNormalizedPoissonExtension_le_majorant
      (σ := (1 : ℝ)) (by norm_num) (by norm_num) (2 * u)
  rw [stripNormalizedPoissonExtension_one] at hbound
  calc
    poissonLogisticDensity u =
      2 * limitingStripPoissonDensity (2 * u) :=
      poissonLogisticDensity_eq_limitingStripPoissonDensity u
    _ ≤ 2 * stripPoissonExponentialMajorant (2 * u) :=
      mul_le_mul_of_nonneg_left hbound.2 (by norm_num)
    _ = Real.pi * Real.exp (-Real.pi * |u|) := by
      unfold stripPoissonExponentialMajorant
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      ring_nf
end CohnElkies
