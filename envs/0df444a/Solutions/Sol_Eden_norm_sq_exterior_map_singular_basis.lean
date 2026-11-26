-- Prove2me | solution 1 for Eden.norm_sq_exterior_map_singular_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:49:07.246408+00:00
-- url     : https://prove2.me/submissions/d8e12f32-0e06-40dc-af3d-c79fcc4b8a45

import Definitions.Def_Eden_ExteriorOperatorNorm
import Definitions.Def_Eden_ExteriorGram
import Theorems.Thm_Eden_inner_exterior_map_gram
import Theorems.Thm_Eden_exterior_gram_basis
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
attribute [local simp] Eden.singularValueFunction_zero
attribute [local simp] Eden.spectralProduct_zero
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open scoped RealInnerProductSpace
open Eden
namespace Eden
theorem _root_.solution (k : ℕ) (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    (v : ExteriorSpace k) :
    ‖exteriorPower.map k A v‖ ^ 2 = ∑ s : ExteriorIndex k,
      (selectedSingularProduct k A s * (singularExteriorBasis k A).repr v s) ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq, inner_exterior_map_gram]
  conv_lhs => arg 3; rw [← (singularExteriorBasis k A).sum_repr v]
  simp only [map_sum, map_smul, exterior_gram_basis, inner_sum,
    real_inner_smul_right, smul_smul]
  apply Finset.sum_congr rfl
  intro s hs
  have hi : ⟪v, singularExteriorBasis k A s⟫ = (singularExteriorBasis k A).repr v s := by
    rw [OrthonormalBasis.repr_apply_apply]
    exact real_inner_comm _ _
  rw [hi]
  ring
end Eden
