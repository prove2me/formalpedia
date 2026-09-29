-- Prove2me | solution 1 for DynamicsRelativity.cross_position_acc_zero
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T01:29:40.068762+00:00
-- url     : https://prove2.me/submissions/8228fecc-7b14-4535-ba5c-db662bbf31a8

import Mathlib
import Definitions.Def_DynamicsRelativity_CentralForces_Defs

open DynamicsRelativity
theorem solution {m : ℝ} {F : ℝ → ℝ} {x : ℝ → Vec} (h : CentralForceMotion m F x) (t : ℝ) :
    cross (x t) (acc x t) = 0 := by
  have hm := h.mass_pos
  have ha : acc x t = (m⁻¹ * (F ‖x t‖ / ‖x t‖)) • x t := by
    have := h.eom t
    rw [mul_smul, ← this, smul_smul, inv_mul_cancel₀ hm.ne', one_smul]
  rw [ha]
  unfold cross
  simp [WithLp.ofLp_smul, map_smul, cross_self]
