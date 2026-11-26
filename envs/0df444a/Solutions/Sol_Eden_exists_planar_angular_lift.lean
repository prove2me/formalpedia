-- Prove2me | solution 1 for Eden.exists_planar_angular_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:11:43.390709+00:00
-- url     : https://prove2.me/submissions/a7146642-236c-4034-9502-a3b884a0c3bc

import Definitions.Def_Eden_PhysicalRadius
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_Eden_AngularLifts
import Theorems.Thm_Eden_planar_evolution_polar
import Theorems.Thm_Eden_exists_initial_polar_angle
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
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
import Theorems.Thm_Eden_radiusEvolution_at_one
import Theorems.Thm_Eden_radiusEvolution_at_sqrt_two
import Theorems.Thm_Eden_radiusEvolution_at_zero
import Theorems.Thm_Eden_radiusEvolution_pos
import Theorems.Thm_Eden_radiusEvolution_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
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
attribute [local simp] Eden.radiusEvolution_at_one
attribute [local simp] Eden.radiusEvolution_at_sqrt_two
attribute [local simp] Eden.radiusEvolution_at_zero
attribute [local simp] Eden.radiusEvolution_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (Ω x y : ℝ) (hxy : x ^ 2 + y ^ 2 ≠ 0) :
    ∃ θ : ℝ,
      (∀ t : ℝ, HasDerivAt (fun τ => θ + Ω * τ) Ω t) ∧
      ∀ t : ℝ, 0 ≤ t →
        0 < radiusEvolution t (Real.sqrt (x ^ 2 + y ^ 2)) ∧
        planarX Ω t x y = radiusEvolution t (Real.sqrt (x ^ 2 + y ^ 2)) *
          Real.cos (θ + Ω * t) ∧
        planarY Ω t x y = radiusEvolution t (Real.sqrt (x ^ 2 + y ^ 2)) *
          Real.sin (θ + Ω * t) := by
  obtain ⟨θ, hx, hy⟩ := exists_initial_polar_angle x y
  refine ⟨θ, ?_, ?_⟩
  · intro t
    have h := (hasDerivAt_const t θ).add ((hasDerivAt_id t).const_mul Ω)
    change HasDerivAt (fun τ => θ + Ω * τ) (0 + Ω * 1) t at h
    simpa only [mul_one, zero_add] using h
  · intro t ht
    refine ⟨radiusEvolution_pos ht (Real.sqrt_pos.2
      (lt_of_le_of_ne (add_nonneg (sq_nonneg x) (sq_nonneg y)) (Ne.symm hxy))), ?_⟩
    have hp := planar_evolution_polar Ω θ ht (Real.sqrt_nonneg (x ^ 2 + y ^ 2))
    rw [← hx, ← hy] at hp
    exact hp
end Eden
