-- Prove2me | solution 1 for Eden.dimH_attractor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:53:12.727662+00:00
-- url     : https://prove2.me/submissions/798e92ad-f1b9-4842-ba38-8600e4ccef16

import Definitions.Def_Eden_HausdorffGeometry
import Definitions.Def_Eden_HausdorffDimensions
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_attractor_subset_range_embedFour
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_dimH_euclideanOpenCube
import Theorems.Thm_Eden_euclideanOpenCube_subset_projectFour
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
open Set MeasureTheory
open scoped ENNReal
open Eden
namespace Eden
theorem _root_.solution : dimH attractor = 4 := by
  apply le_antisymm
  · calc
      dimH attractor ≤ dimH (range embedFour) := dimH_mono attractor_subset_range_embedFour
      _ ≤ 4 := by
        simpa only [LinearMap.coe_toContinuousLinearMap', finrank_euclideanSpace_fin, Nat.cast_ofNat] using
          embedFour.toContinuousLinearMap.contDiff.dimH_range_le
  · calc
      (4 : ℝ≥0∞) = dimH (euclideanOpenCube 4) := (dimH_euclideanOpenCube 4).symm
      _ ≤ dimH (projectFour '' attractor) := dimH_mono euclideanOpenCube_subset_projectFour
      _ ≤ dimH attractor := projectFour.toContinuousLinearMap.lipschitz.dimH_image_le attractor
end Eden
