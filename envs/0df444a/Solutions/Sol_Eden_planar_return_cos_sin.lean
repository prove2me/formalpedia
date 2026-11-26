-- Prove2me | solution 1 for Eden.planar_return_cos_sin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:14:58.993854+00:00
-- url     : https://prove2.me/submissions/dd149fc0-99ca-4fef-a915-989c61c9d846

import Definitions.Def_Eden_RadialReturns
import Mathlib.NumberTheory.Real.Irrational
import Definitions.Def_Eden_RotationReturns
import Theorems.Thm_Eden_rotation_fixed_iff
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_at_one
import Theorems.Thm_Eden_planarAmplitude_at_two
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_planar_radius_sq
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_eq_self_iff
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.diagonalLinear_apply
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialAmplitude_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (Ω : ℝ) {t x y : ℝ} (ht : 0 < t)
    (hs : x ^ 2 + y ^ 2 ≠ 0)
    (hx : planarX Ω t x y = x) (hy : planarY Ω t x y = y) :
    Real.cos (Ω * t) = 1 ∧ Real.sin (Ω * t) = 0 := by
  have hr : squaredRadiusEvolution t (x ^ 2 + y ^ 2) = x ^ 2 + y ^ 2 := by
    rw [← planar_radius_sq Ω ht.le, hx, hy]
  have hstationary := (squaredRadiusEvolution_eq_self_iff ht).mp hr
  have hg : planarAmplitude t (x ^ 2 + y ^ 2) = 1 := by
    rcases hstationary with h₀ | h₁ | h₂
    · exact False.elim (hs h₀)
    · rw [h₁, planarAmplitude_at_one ht.le]
    · rw [h₂, planarAmplitude_at_two ht.le]
  apply (rotation_fixed_iff hs).mp
  constructor
  · simpa only [planarX, hg, one_mul] using hx
  · simpa only [planarY, hg, one_mul] using hy
end Eden
