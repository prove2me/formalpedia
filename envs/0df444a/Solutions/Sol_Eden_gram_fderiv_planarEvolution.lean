-- Prove2me | solution 1 for Eden.gram_fderiv_planarEvolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:39:47.716055+00:00
-- url     : https://prove2.me/submissions/8125f03a-a23b-4678-947f-14b9312e326e

import Definitions.Def_Eden_PlanarDerivative
import Definitions.Def_Eden_StationaryFactors
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Definitions.Def_Eden_PlanarSingularValues
import Theorems.Thm_Eden_adjoint_planarDiagonal
import Theorems.Thm_Eden_fderiv_planarEvolution_orthogonal_decomposition
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarDiagonal_apply
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
attribute [local simp] Eden.planarDiagonal_apply
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
open Polynomial
open Eden
namespace Eden
theorem _root_.solution (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PlanarSpace) :
    (fderiv ℝ (planarEvolution Ω t) p).toLinearMap.adjoint ∘ₗ
        (fderiv ℝ (planarEvolution Ω t) p).toLinearMap =
      (planarRadialFrame p).toLinearEquiv.conj
        (planarDiagonal (WithLp.toLp 2 (fun i => planarFactors t p i ^ 2))) := by
  rw [fderiv_planarEvolution_orthogonal_decomposition Ω ht p]
  simp only [LinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_toLinearMap_eq_symm,
    adjoint_planarDiagonal]
  ext v i
  simp [LinearEquiv.conj_apply_apply, planarDiagonal, pow_two, mul_assoc]
end Eden
