-- Prove2me | solution 1 for Eden.singularValues_fderiv_planarEvolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:41:18.655878+00:00
-- url     : https://prove2.me/submissions/b1befd9d-40e6-423c-9cb7-1a9f70a8498c

import Definitions.Def_Eden_PlanarDerivative
import Definitions.Def_Eden_StationaryFactors
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Definitions.Def_Eden_PlanarSingularValues
import Theorems.Thm_Eden_roots_charpoly_planarDiagonal
import Theorems.Thm_Eden_gram_fderiv_planarEvolution
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_pos
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarDiagonal_apply
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_pos
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
theorem _root_.solution (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PlanarSpace) :
    Finset.univ.val.map (fun i : Fin 2 =>
      (fderiv ℝ (planarEvolution Ω t) p).toLinearMap.singularValues i) =
      Finset.univ.val.map (fun i : Fin 2 => planarFactors t p i) := by
  let T := (fderiv ℝ (planarEvolution Ω t) p).toLinearMap
  have hn : Module.finrank ℝ PlanarSpace = 2 := finrank_euclideanSpace_fin
  have hroots := T.isSymmetric_adjoint_comp_self.roots_charpoly_eq_eigenvalues hn
  have hgram : (T.adjoint ∘ₗ T).charpoly.roots =
      Finset.univ.val.map (fun i : Fin 2 => planarFactors t p i ^ 2) := by
    rw [gram_fderiv_planarEvolution Ω ht p, LinearEquiv.charpoly_conj,
      roots_charpoly_planarDiagonal]
  have hev : Finset.univ.val.map (fun i : Fin 2 =>
      T.isSymmetric_adjoint_comp_self.eigenvalues hn i) =
      Finset.univ.val.map (fun i : Fin 2 => planarFactors t p i ^ 2) := by
    simpa using hroots.symm.trans hgram
  have hnonneg (i : Fin 2) : 0 ≤ planarFactors t p i := by
    fin_cases i
    · exact (radialAmplitude_pos ht (add_nonneg (sq_nonneg _) (sq_nonneg _))).le
    · exact (planarAmplitude_pos ht (add_nonneg (sq_nonneg _) (sq_nonneg _))).le
  have hsqrt := congrArg (Multiset.map Real.sqrt) hev
  simpa only [Multiset.map_map, Function.comp_def, ← T.singularValues_fin hn,
    Real.sqrt_sq (hnonneg _)] using hsqrt
end Eden
