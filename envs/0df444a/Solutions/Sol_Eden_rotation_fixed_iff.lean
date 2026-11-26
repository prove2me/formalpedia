-- Prove2me | solution 1 for Eden.rotation_fixed_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:13:56.523637+00:00
-- url     : https://prove2.me/submissions/e3934ac1-1262-4df4-9df2-1caf6ed6ce0d

import Definitions.Def_Eden_RadialReturns
import Mathlib.NumberTheory.Real.Irrational
import Definitions.Def_Eden_RotationReturns
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
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
theorem _root_.solution {x y θ : ℝ} (hs : x ^ 2 + y ^ 2 ≠ 0) :
    (x * Real.cos θ - y * Real.sin θ = x ∧
      x * Real.sin θ + y * Real.cos θ = y) ↔
      Real.cos θ = 1 ∧ Real.sin θ = 0 := by
  constructor
  · rintro ⟨hx, hy⟩
    have hprod : (x ^ 2 + y ^ 2) * (Real.cos θ - 1) = 0 := by
      nlinarith [congrArg (fun a : ℝ => x * a) hx,
        congrArg (fun a : ℝ => y * a) hy]
    have hcos : Real.cos θ = 1 := by
      have := (mul_eq_zero.mp hprod).resolve_left hs
      linarith
    refine ⟨hcos, ?_⟩
    have hid := Real.sin_sq_add_cos_sq θ
    rw [hcos] at hid
    nlinarith [sq_nonneg (Real.sin θ)]
  · rintro ⟨hc, hs⟩
    simp [hc, hs]
end Eden
