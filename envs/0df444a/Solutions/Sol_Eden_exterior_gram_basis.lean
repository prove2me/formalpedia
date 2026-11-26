-- Prove2me | solution 1 for Eden.exterior_gram_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:47:06.219148+00:00
-- url     : https://prove2.me/submissions/58ceda84-67ba-4750-b87e-e75db04b5069

import Definitions.Def_Eden_ExteriorOperatorNorm
import Definitions.Def_Eden_ExteriorGram
import Theorems.Thm_Eden_singularExteriorBasis_apply
import Theorems.Thm_Eden_gram_singularVectorBasis
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
    (s : ExteriorIndex k) :
    exteriorPower.map k (A.adjoint ∘ₗ A) (singularExteriorBasis k A s) =
      selectedSingularProduct k A s ^ 2 • singularExteriorBasis k A s := by
  change exteriorPower.map k (A.adjoint ∘ₗ A)
      (((singularVectorBasis A).exteriorPower k).toBasis s) = _
  simp only [OrthonormalBasis.toBasis_exteriorPower, exteriorPower.basis_apply,
    exteriorPower.ιMulti_family, exteriorPower.map_apply_ιMulti, Function.comp_def,
    OrthonormalBasis.coe_toBasis]
  simp_rw [gram_singularVectorBasis]
  rw [AlternatingMap.map_smul_univ, Finset.prod_pow]
  rw [singularExteriorBasis_apply, exteriorPower.ιMulti_family]
  rfl
end Eden
