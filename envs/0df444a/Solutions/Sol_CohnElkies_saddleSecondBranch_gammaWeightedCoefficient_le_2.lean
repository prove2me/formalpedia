-- Prove2me | solution 2 for CohnElkies.saddleSecondBranch_gammaWeightedCoefficient_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:28:39.213908+00:00
-- url     : https://prove2.me/submissions/00b52b9f-ad56-4e8a-94c2-3761b2b87a87

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology


theorem solution
    {q η C : ℝ}
    (hq : 0 < q)
    (hη : 1 ≤ η)
    (hC : 0 < C)
    (hrate : 1 / q ≤ C * η) :
    2 * max (1 : ℝ)
        ((Real.sqrt (q / 6) ^ 3)⁻¹) *
      Real.sqrt (Real.pi / (q / 2)) ≤
        (2 * (1 + (6 * C) ^ 3) *
          (1 + 2 * Real.pi * C)) * η ^ 4 := by
  have hpi := Real.pi_pos
  have hr : 0 < Real.sqrt (q / 6) := Real.sqrt_pos.2 (by positivity)
  have hr2 : Real.sqrt (q / 6) ^ 2 = q / 6 := Real.sq_sqrt (by positivity)
  have ht : 0 < (Real.sqrt (q / 6) ^ 3)⁻¹ := by positivity
  have ht2 : ((Real.sqrt (q / 6) ^ 3)⁻¹) ^ 2 = (6 / q) ^ 3 := by
    rw [inv_pow, ← pow_mul, show Real.sqrt (q / 6) ^ (3 * 2) = (Real.sqrt (q / 6) ^ 2) ^ 3 by ring, hr2]
    field_simp
  have h6 : 6 / q ≤ 6 * C * η := by
    have : 6 / q = 6 * (1 / q) := by ring
    nlinarith
  have h6' : (6 / q) ^ 3 ≤ (6 * C * η) ^ 3 := pow_le_pow_left₀ (by positivity) h6 3
  have hη3 : 1 ≤ η ^ 3 := one_le_pow₀ hη
  have hC3 : 0 ≤ (6 * C) ^ 3 := by positivity
  have hmax : max (1 : ℝ) ((Real.sqrt (q / 6) ^ 3)⁻¹) ≤ (1 + (6 * C) ^ 3) * η ^ 3 := by
    apply max_le
    · nlinarith
    · have h1 : (Real.sqrt (q / 6) ^ 3)⁻¹ ≤ 1 + ((Real.sqrt (q / 6) ^ 3)⁻¹) ^ 2 := by
        nlinarith [sq_nonneg ((Real.sqrt (q / 6) ^ 3)⁻¹ - 1)]
      rw [ht2] at h1
      have : (6 * C * η) ^ 3 = (6 * C) ^ 3 * η ^ 3 := by ring
      nlinarith
  have hx : Real.pi / (q / 2) ≤ 2 * Real.pi * C * η := by
    have : Real.pi / (q / 2) = 2 * Real.pi * (1 / q) := by field_simp
    rw [this]
    have := mul_le_mul_of_nonneg_left hrate (by positivity : (0:ℝ) ≤ 2 * Real.pi)
    linarith
  have hs : Real.sqrt (Real.pi / (q / 2)) ≤ (1 + 2 * Real.pi * C) * η := by
    rw [Real.sqrt_le_iff]
    have hx0 : 0 ≤ Real.pi / (q / 2) := by positivity
    have hη0 : (0:ℝ) ≤ η := by linarith
    constructor
    · positivity
    · nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi * C) hη0]
  have hm0 : 0 ≤ max (1 : ℝ) ((Real.sqrt (q / 6) ^ 3)⁻¹) := le_trans zero_le_one (le_max_left _ _)
  calc 2 * max (1 : ℝ) ((Real.sqrt (q / 6) ^ 3)⁻¹) * Real.sqrt (Real.pi / (q / 2))
      ≤ 2 * ((1 + (6 * C) ^ 3) * η ^ 3) * ((1 + 2 * Real.pi * C) * η) := by
        apply mul_le_mul (by linarith) hs (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by ring

