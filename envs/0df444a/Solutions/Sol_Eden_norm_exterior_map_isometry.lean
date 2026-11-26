-- Prove2me | solution 1 for Eden.norm_exterior_map_isometry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:27:11.881314+00:00
-- url     : https://prove2.me/submissions/ebe97773-7fd3-4131-8462-277bc61d2b5d

import Definitions.Def_Eden_DerivativeDecomposition
import Mathlib.Analysis.InnerProductSpace.ExteriorPower
import Definitions.Def_Eden_ExteriorGeometry
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
theorem _root_.solution (k : ℕ) (U : PhaseSpace ≃ₗᵢ[ℝ] PhaseSpace)
    (v : ExteriorSpace k) : ‖exteriorPower.map k U.toLinearMap v‖ = ‖v‖ := by
  let b := EuclideanSpace.basisFun (Fin 5) ℝ
  let B := b.exteriorPower k
  let C := (b.map U).exteriorPower k
  let V := B.equiv C (Equiv.refl _)
  have hm : exteriorPower.map k U.toLinearMap = V.toLinearMap := by
    apply B.toBasis.ext
    intro s
    change exteriorPower.map k U.toLinearMap (B s) = V (B s)
    rw [OrthonormalBasis.equiv_apply_basis]
    change exteriorPower.map k U.toLinearMap (B.toBasis s) = C.toBasis s
    simp only [B, C, OrthonormalBasis.toBasis_exteriorPower, exteriorPower.basis_apply,
      exteriorPower.map_apply_ιMulti_family, OrthonormalBasis.coe_toBasis]
    rfl
  rw [hm]
  exact V.norm_map v
end Eden
