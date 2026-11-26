-- Prove2me | solution 1 for Eden.dimH_torus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:53:44.788523+00:00
-- url     : https://prove2.me/submissions/bbedb5d3-6833-4a37-bd6d-b9a1e9a6b7e3

import Definitions.Def_Eden_HausdorffGeometry
import Definitions.Def_Eden_HausdorffDimensions
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_contDiff_torusParametrization
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_dimH_euclideanOpenCube
import Theorems.Thm_Eden_euclideanOpenCube_subset_projectTorus
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
import Theorems.Thm_Eden_range_torusParametrization
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
theorem _root_.solution : dimH torus = 2 := by
  apply le_antisymm
  · rw [← range_torusParametrization]
    simpa only [finrank_euclideanSpace_fin, Nat.cast_ofNat] using
      (contDiff_torusParametrization 1).dimH_range_le
  · calc
      (2 : ℝ≥0∞) = dimH (euclideanOpenCube 2) := (dimH_euclideanOpenCube 2).symm
      _ ≤ dimH (projectTorus '' torus) := dimH_mono euclideanOpenCube_subset_projectTorus
      _ ≤ dimH torus := projectTorus.toContinuousLinearMap.lipschitz.dimH_image_le torus
end Eden
