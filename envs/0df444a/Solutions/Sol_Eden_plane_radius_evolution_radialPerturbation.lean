-- Prove2me | solution 1 for Eden.plane_radius_evolution_radialPerturbation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:58:43.495421+00:00
-- url     : https://prove2.me/submissions/d6c06a9b-ba53-472c-b520-dbd6a9ed5901

import Definitions.Def_Eden_UniformAttraction
import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_InstabilityGeometry
import Theorems.Thm_Eden_norm_planeProjection
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_origin
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
import Theorems.Thm_Eden_radiusEvolution_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
import Theorems.Thm_P2M_Eden_radius__evolution_5f79e8068ad6
import Theorems.Thm_P2M_Eden_radius__evolution_affebfa495cb
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
open Set
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (j : Fin 2)
    {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) (s : ℝ) :
    ‖planeProjection j (evolution c t (radialPerturbation j r s))‖ = radiusEvolution t r := by
  rw [norm_planeProjection]
  fin_cases j
  · change Real.sqrt (radiusSq₁ (evolution c t (radialPerturbation 0 r s))) = _
    rw [radius₁_evolution c ht]
    simp [radialPerturbation, radiusSq₁, Real.sqrt_sq hr]
  · change Real.sqrt (radiusSq₂ (evolution c t (radialPerturbation 1 r s))) = _
    rw [radius₂_evolution c ht]
    simp [radialPerturbation, radiusSq₂, Real.sqrt_sq hr]
end Eden
