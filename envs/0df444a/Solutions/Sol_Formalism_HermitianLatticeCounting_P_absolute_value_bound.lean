-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.absolute_value_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:13.5909+00:00
-- url     : https://prove2.me/submissions/cac20261-38b9-4315-805a-f3a125a17a7a

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SchurAverage
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_sqrt_det_gram_eq_prod_norm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_norm_det_sesquilinear_le_gramSchmidt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open InnerProductSpace
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : AbsA := by
  intro U₁ U₂ _ _ _ _ r u u' Z hZ
  let B : U₁ →ₗ[ℂ] U₂ →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun w₁ w₂ => ∑ a, ∑ b, inner ℂ (u a) w₁ * conj (inner ℂ (u' b) w₂) * Z a b)
    (by intro x x' y; simp only [inner_add_right, add_mul, Finset.sum_add_distrib])
    (by intro c x y; simp only [inner_smul_right, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    (by intro x y y'; simp only [inner_add_right, map_add, mul_add, add_mul, Finset.sum_add_distrib])
    (by intro c x y; simp only [inner_smul_right, map_mul, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
  have hBapp : ∀ w₁ w₂, B w₁ w₂ =
      ∑ a, ∑ b, inner ℂ (u a) w₁ * conj (inner ℂ (u' b) w₂) * Z a b := fun _ _ => rfl
  have hW := norm_det_sesquilinear_le_gramSchmidt B 2 (by norm_num) (fun x y => by rw [hBapp]; exact hZ x y) u u'
  rw [← sqrt_det_gram_eq_prod_norm, ← sqrt_det_gram_eq_prod_norm] at hW
  have hM : (Matrix.of fun c d => B (u c) (u' d)) =
      (Matrix.gram ℂ u)ᵀ * Z * ((starRingEnd ℂ).mapMatrix (Matrix.gram ℂ u')) := by
    ext c d
    simp only [Matrix.of_apply, hBapp, Matrix.mul_apply, Matrix.transpose_apply, Matrix.gram_apply,
      RingHom.mapMatrix_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det, norm_mul, norm_mul,
    RCLike.norm_conj] at hW
  set X := Real.sqrt ‖(Matrix.gram ℂ u).det‖ with hX
  set X' := Real.sqrt ‖(Matrix.gram ℂ u').det‖ with hX'
  have hX2 : ‖(Matrix.gram ℂ u).det‖ = X * X := (Real.mul_self_sqrt (norm_nonneg _)).symm
  have hX2' : ‖(Matrix.gram ℂ u').det‖ = X' * X' := (Real.mul_self_sqrt (norm_nonneg _)).symm
  rw [hX2, hX2'] at hW
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hX0' : 0 ≤ X' := Real.sqrt_nonneg _
  rcases (mul_nonneg hX0 hX0').lt_or_eq with hp | hz
  · have : (X * X') * (X * X' * ‖Z.det‖) ≤ (X * X') * 2 ^ r := by nlinarith
    exact le_of_mul_le_mul_left this hp
  · rw [← hz, zero_mul]; positivity
end Formalism.HermitianLatticeCounting.P
