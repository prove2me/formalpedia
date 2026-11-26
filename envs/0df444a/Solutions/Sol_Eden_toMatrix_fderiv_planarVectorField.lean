-- Prove2me | solution 1 for Eden.toMatrix_fderiv_planarVectorField
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:10:51.716192+00:00
-- url     : https://prove2.me/submissions/ac560eab-95c1-4be8-bf6d-63f17bd798fd

import Definitions.Def_Eden_VectorFieldDerivative
import Definitions.Def_Eden_PlanarVectorField
import Theorems.Thm_Eden_fderiv_planarVectorField_apply
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
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
theorem _root_.solution (Ω : ℝ) (p : PlanarSpace) :
    (fderiv ℝ (planarVectorField Ω) p).toLinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis =
      q (p 0 ^ 2 + p 1 ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (2 * deriv q (p 0 ^ 2 + p 1 ^ 2)) •
          Matrix.vecMulVec (fun i => p i) (fun i => p i) +
        Ω • !![0, -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply,
      OrthonormalBasis.coe_toBasis_repr_apply,
      fderiv_planarVectorField_apply, Matrix.vecMulVec] <;> ring
end Eden
