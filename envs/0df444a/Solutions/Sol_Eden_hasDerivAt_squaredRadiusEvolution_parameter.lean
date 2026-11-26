-- Prove2me | solution 1 for Eden.hasDerivAt_squaredRadiusEvolution_parameter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:08:07.366265+00:00
-- url     : https://prove2.me/submissions/dabe21b7-dd21-4e04-a48e-3812869a1e1f

import Definitions.Def_Eden_ScalarFlow
import Mathlib.Tactic.FunProp
import Definitions.Def_Eden_ScalarCalculus
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_pos
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_sqrt_radialDiscriminant_pos
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open scoped Topology
open Filter
open Eden
namespace Eden
theorem _root_.solution {t : ℝ} (ht : 0 ≤ t) (s : ℝ) :
    HasDerivAt (squaredRadiusEvolution t)
      (Real.exp (-4 * t) / Real.sqrt (radialDiscriminant t s) ^ 3) s := by
  have hu := (hasDerivAt_id s).sub_const 1
  have hd := ((hu.pow 2).const_mul (1 - Real.exp (-4 * t))).const_add
    (Real.exp (-4 * t))
  have hr := hd.sqrt (ne_of_gt (radialDiscriminant_pos ht s))
  have hR := sqrt_radialDiscriminant_pos ht s
  have hq := hu.div hr (ne_of_gt hR)
  have hsq := Real.sq_sqrt (le_of_lt (radialDiscriminant_pos ht s))
  apply (hq.const_add 1).congr_deriv
  dsimp [radialDiscriminant] at hR hsq ⊢
  simp only [neg_mul] at hR hsq ⊢
  field_simp [ne_of_gt hR]
  nlinarith
end Eden
