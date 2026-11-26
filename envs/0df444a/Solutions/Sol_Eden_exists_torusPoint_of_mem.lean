-- Prove2me | solution 1 for Eden.exists_torusPoint_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:07:45.084647+00:00
-- url     : https://prove2.me/submissions/144c2db3-9687-4e9e-9751-abe7c4babb1b

import Definitions.Def_Eden_CircleOrbits
import Definitions.Def_Eden_TorusAngles
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_origin
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_exists_positive_rotation_between
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
theorem _root_.solution {p : PhaseSpace} (hp : p ∈ torus) :
    ∃ θ₁ θ₂ : ℝ, torusPoint θ₁ θ₂ = p := by
  obtain ⟨θ₁, _, hx₁, hy₁⟩ := exists_positive_rotation_between
    (show (0 : ℝ) < 1 by norm_num) (x := 1) (y := 0) (by norm_num) hp.1
  obtain ⟨θ₂, _, hx₂, hy₂⟩ := exists_positive_rotation_between
    (show (0 : ℝ) < 1 by norm_num) (x := 1) (y := 0) (by norm_num) hp.2.1
  simp only [one_mul, zero_mul, sub_zero, add_zero] at hx₁ hy₁ hx₂ hy₂
  refine ⟨θ₁, θ₂, ?_⟩
  ext i
  fin_cases i <;> simp [torusPoint, hx₁, hy₁, hx₂, hy₂, hp.2.2]
end Eden
