-- Prove2me | solution 1 for Eden.exists_planar_time_on_stationary_radius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:00:56.220375+00:00
-- url     : https://prove2.me/submissions/b5f344b2-423d-4968-8093-155957f4bc35

import Definitions.Def_Eden_PeriodicSets
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_Eden_CircleOrbits
import Theorems.Thm_Eden_exists_positive_rotation_between
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_origin
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_at_one
import Theorems.Thm_Eden_planarAmplitude_at_two
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
attribute [local simp] Eden.evolution_origin
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
open Set
open Eden
namespace Eden
theorem _root_.solution {Ω s x y u v : ℝ}
    (hΩ : 0 < Ω) (hs : s = 1 ∨ s = 2)
    (hxy : x ^ 2 + y ^ 2 = s) (huv : u ^ 2 + v ^ 2 = s) :
    ∃ t : ℝ, 0 < t ∧ planarX Ω t x y = u ∧ planarY Ω t x y = v := by
  have hs₀ : 0 < s := by rcases hs with rfl | rfl <;> norm_num
  obtain ⟨θ, hθ, hx, hy⟩ := exists_positive_rotation_between hs₀ hxy huv
  have ht : 0 < θ / Ω := div_pos hθ hΩ
  have hangle : Ω * (θ / Ω) = θ := by field_simp
  have hg : planarAmplitude (θ / Ω) (x ^ 2 + y ^ 2) = 1 := by
    rw [hxy]
    rcases hs with rfl | rfl
    · exact planarAmplitude_at_one ht.le
    · exact planarAmplitude_at_two ht.le
  exact ⟨θ / Ω, ht, by simpa only [planarX, hg, one_mul, hangle] using hx,
    by simpa only [planarY, hg, one_mul, hangle] using hy⟩
end Eden
