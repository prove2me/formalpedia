-- Prove2me | solution 1 for DistanceGeometry.det_centeredGram_block_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:46:56.50039+00:00
-- url     : https://prove2.me/submissions/517e7884-1432-4123-9e83-a9afa65da0e9

module
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
public import Definitions.Def_LeanPool_DistanceGeometry_Schoenberg
public import Definitions.Def_LeanPool_DistanceGeometry_CayleyMengerVolume
public import Theorems.Thm_DistanceGeometry_centeredGram_apply_eq_inner

section
@[expose] public section
namespace DistanceGeometry
open Matrix
open scoped RealInnerProductSpace
variable {n : ℕ}
private theorem real_scalar_inner (a b : ℝ) : ⟪a, b⟫ = a * b := by
  exact RCLike.inner_apply' a b
private theorem inner_fin_two (u v : EuclideanSpace ℝ (Fin 2)) :
    ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two, real_scalar_inner, real_scalar_inner]
end DistanceGeometry
end
end

set_option autoImplicit true
@[expose] public section
public section
open DistanceGeometry
open Matrix
open scoped RealInnerProductSpace
variable {n : ℕ}
namespace DistanceGeometry
theorem _root_.solution
    {D : Matrix (Fin 3) (Fin 3) ℝ} {x : Fin 3 → EuclideanSpace ℝ (Fin 2)}
    (hD : IsSqDistMatrix D x) :
    centeredGram D 1 1 * centeredGram D 2 2 - (centeredGram D 1 2) ^ 2
      = ((x 1 - x 0) 0 * (x 2 - x 0) 1 - (x 1 - x 0) 1 * (x 2 - x 0) 0) ^ 2 := by
  rw [centeredGram_apply_eq_inner hD 1 1, centeredGram_apply_eq_inner hD 2 2,
      centeredGram_apply_eq_inner hD 1 2, inner_fin_two, inner_fin_two, inner_fin_two]
  ring
end DistanceGeometry
