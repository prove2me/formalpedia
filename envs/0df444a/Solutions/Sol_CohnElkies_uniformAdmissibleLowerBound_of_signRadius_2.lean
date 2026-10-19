-- Prove2me | solution 2 for CohnElkies.uniformAdmissibleLowerBound_of_signRadius
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:01:53.987698+00:00
-- url     : https://prove2.me/submissions/b0068ec2-70e9-4873-9ff9-332c6a607b5b

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology


theorem solution
    (hsign : UniformAntiFourierSignRadius) :
    UniformAdmissibleLowerBound := by
  intro c hc
  rcases le_or_gt c 0 with hc0 | hc0
  · refine Filter.Eventually.of_forall fun d f => le_trans hc0 ?_
    unfold normalizedCost quotient
    exact div_nonneg (Real.rpow_nonneg (div_pos (admissible_zero_pos f) f.fourier_zero_pos).le _)
      (Real.sqrt_nonneg _)
  · filter_upwards [hsign c hc0 hc, Filter.eventually_gt_atTop 0] with d hd hdpos f
    by_contra hlt
    push_neg at hlt
    have hs : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hdpos)
    have hR : (balancingScale f)⁻¹ ≤ c * Real.sqrt d := by
      have : (balancingScale f)⁻¹ = quotient f ^ ((d:ℝ)⁻¹) := by
        unfold balancingScale quotient
        rw [← Real.inv_rpow (div_pos f.fourier_zero_pos (admissible_zero_pos f)).le, inv_div]
      rw [this]
      unfold normalizedCost at hlt
      rw [div_lt_iff₀ hs] at hlt
      exact hlt.le
    exact hd.false ((balancedAntiFourierWitness f hdpos).monoRadius hR)

