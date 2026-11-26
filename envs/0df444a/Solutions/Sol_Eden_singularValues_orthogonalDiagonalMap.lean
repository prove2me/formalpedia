-- Prove2me | solution 1 for Eden.singularValues_orthogonalDiagonalMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:38:04.950027+00:00
-- url     : https://prove2.me/submissions/8e2c4c96-3aa6-48ab-a4a5-fd20808431b1

import Definitions.Def_Eden_DerivativeDecomposition
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Definitions.Def_Eden_SingularValues
import Theorems.Thm_Eden_roots_charpoly_gram_orthogonalDiagonalMap
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
open Polynomial
open Eden
namespace Eden
theorem _root_.solution
    (U V : PhaseSpace ≃ₗᵢ[ℝ] PhaseSpace) (d : PhaseSpace) (hd : ∀ i, 0 ≤ d i) :
    Finset.univ.val.map (fun i : Fin 5 => (orthogonalDiagonalMap U V d).singularValues i) =
      Finset.univ.val.map (fun i : Fin 5 => d i) := by
  let T := orthogonalDiagonalMap U V d
  have hn : Module.finrank ℝ PhaseSpace = 5 := finrank_euclideanSpace_fin
  have hroots := T.isSymmetric_adjoint_comp_self.roots_charpoly_eq_eigenvalues hn
  have hgram := roots_charpoly_gram_orthogonalDiagonalMap U V d
  have hev : Finset.univ.val.map (fun i : Fin 5 =>
      T.isSymmetric_adjoint_comp_self.eigenvalues hn i) =
      Finset.univ.val.map (fun i : Fin 5 => d i ^ 2) := by
    simpa using hroots.symm.trans hgram
  have hsqrt := congrArg (Multiset.map Real.sqrt) hev
  simpa only [Multiset.map_map, Function.comp_def, ← T.singularValues_fin hn,
    Real.sqrt_sq (hd _)] using hsqrt
end Eden
