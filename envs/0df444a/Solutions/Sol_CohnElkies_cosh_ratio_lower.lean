-- Prove2me | solution 1 for CohnElkies.cosh_ratio_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/d23494b4-b65c-4a5b-91f3-4b917203f8ed

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped ContDiff FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) :
    Real.exp (δ * a) / 2 ≤
      Real.cosh ((1 + δ) * a) / Real.cosh a := by
  apply (le_div_iff₀ (Real.cosh_pos a)).2
  rw [show (1 + δ) * a = a + δ * a by ring, Real.cosh_add]
  have hq : Real.exp (δ * a) / 2 ≤ Real.cosh (δ * a) := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-(δ * a))]
  calc
    Real.exp (δ * a) / 2 * Real.cosh a =
        Real.cosh a * (Real.exp (δ * a) / 2) := by ring
    _ ≤ Real.cosh a * Real.cosh (δ * a) := by
      exact mul_le_mul_of_nonneg_left hq (Real.cosh_pos a).le
    _ ≤ Real.cosh a * Real.cosh (δ * a) +
          Real.sinh a * Real.sinh (δ * a) := by
      apply le_add_of_nonneg_right
      exact mul_nonneg (Real.sinh_nonneg_iff.mpr ha)
        (Real.sinh_nonneg_iff.mpr (mul_nonneg hδ ha))
end CohnElkies
