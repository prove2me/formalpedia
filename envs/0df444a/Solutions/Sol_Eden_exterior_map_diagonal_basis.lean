-- Prove2me | solution 1 for Eden.exterior_map_diagonal_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:31:47.409537+00:00
-- url     : https://prove2.me/submissions/be5f5335-ee50-4547-a930-00c22c7b8289

import Definitions.Def_Eden_DerivativeDecomposition
import Mathlib.Analysis.InnerProductSpace.ExteriorPower
import Definitions.Def_Eden_ExteriorGeometry
import Theorems.Thm_Eden_exteriorBasis_apply
import Theorems.Thm_Eden_diagonalLinear_basis
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
theorem _root_.solution (k : ℕ) (d : PhaseSpace) (s : ExteriorIndex k) :
    exteriorPower.map k (diagonalLinear d) (exteriorBasis k s) =
      exteriorFactor k d s • exteriorBasis k s := by
  change exteriorPower.map k (diagonalLinear d)
      (((EuclideanSpace.basisFun (Fin 5) ℝ).exteriorPower k).toBasis s) = _
  simp only [OrthonormalBasis.toBasis_exteriorPower, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family, exteriorPower.map_apply_ιMulti, Function.comp_def,
    OrthonormalBasis.coe_toBasis]
  simp_rw [diagonalLinear_basis]
  rw [AlternatingMap.map_smul_univ]
  rw [exteriorBasis_apply, exteriorPower.ιMulti_family]
  rfl
end Eden
