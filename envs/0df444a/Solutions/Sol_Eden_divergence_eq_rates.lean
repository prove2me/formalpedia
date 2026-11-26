-- Prove2me | solution 1 for Eden.divergence_eq_rates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:26:59.177869+00:00
-- url     : https://prove2.me/submissions/c4257b49-67e8-47a6-b788-23bcac788d65

import Definitions.Def_Eden_VectorFieldDerivative
import Definitions.Def_Eden_Divergence
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_fderiv_vectorField_apply
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_radialRate_eq_q_add_deriv
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
import Theorems.Thm_Eden_tangentialRate_eq_q
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
theorem _root_.solution (c : ℝ) (p : PhaseSpace) :
    divergence c p = radialRate (radiusSq₁ p) + tangentialRate (radiusSq₁ p) +
      radialRate (radiusSq₂ p) + tangentialRate (radiusSq₂ p) - c := by
  unfold divergence
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis]
  simp [Matrix.trace, LinearMap.toMatrix_apply, EuclideanSpace.basisFun_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, PiLp.single_apply, Fin.sum_univ_succ,
    fderiv_vectorField_apply, radialRate_eq_q_add_deriv, tangentialRate_eq_q]
  dsimp [radiusSq₁, radiusSq₂]
  ring
end Eden
