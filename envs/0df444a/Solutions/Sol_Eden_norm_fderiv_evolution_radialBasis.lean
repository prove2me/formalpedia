-- Prove2me | solution 1 for Eden.norm_fderiv_evolution_radialBasis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:54:16.675122+00:00
-- url     : https://prove2.me/submissions/9513c4f2-b3e8-4c07-9a46-6526e4236227

import Definitions.Def_Eden_StationaryFactors
import Definitions.Def_Eden_ExponentSums
import Definitions.Def_Eden_HausdorffDimensions
import Definitions.Def_Eden_TorusDirections
import Theorems.Thm_Eden_diagonalLinear_basisFun
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_derivativeFactors_pos
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_origin
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_fderiv_evolution_radialFrame
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDefect_at_one
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_singularValueFunction_zero
import Theorems.Thm_Eden_spectralProduct_zero
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
attribute [local simp] Eden.radialDefect_at_one
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.singularValueFunction_zero
attribute [local simp] Eden.spectralProduct_zero
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Set Filter Topology MeasureTheory
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace) (i : Fin 5) :
    ‖fderiv ℝ (evolution c t) p (radialOrthonormalBasis p i)‖ = derivativeFactors c t p i := by
  change ‖fderiv ℝ (evolution c t) p (radialFrame p (EuclideanSpace.basisFun (Fin 5) ℝ i))‖ = _
  rw [fderiv_evolution_radialFrame c ht, (angularRotation t).norm_map,
    (radialFrame p).norm_map, diagonalLinear_basisFun, norm_smul,
    (EuclideanSpace.basisFun (Fin 5) ℝ).orthonormal.norm_eq_one]
  simp [Real.norm_eq_abs, abs_of_pos (derivativeFactors_pos c ht p i)]
end Eden
