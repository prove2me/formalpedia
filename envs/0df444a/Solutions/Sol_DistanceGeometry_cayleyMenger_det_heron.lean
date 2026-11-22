-- Prove2me | solution 1 for DistanceGeometry.cayleyMenger_det_heron
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:48:21.907184+00:00
-- url     : https://prove2.me/submissions/47c92b5a-f359-4a59-92f8-d186f66596e9

module
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
public import Definitions.Def_LeanPool_DistanceGeometry_Schoenberg
public import Definitions.Def_LeanPool_DistanceGeometry_CayleyMengerVolume
public import Theorems.Thm_DistanceGeometry_cayleyMenger_det_triangle_centeredGram
public import Theorems.Thm_DistanceGeometry_det_centeredGram_block_eq_sq
public import Theorems.Thm_DistanceGeometry_IsPreDistMatrix_hollow
public import Theorems.Thm_DistanceGeometry_IsPreDistMatrix_symm
public import Theorems.Thm_DistanceGeometry_IsSqDistMatrix_hollow
public import Theorems.Thm_DistanceGeometry_IsSqDistMatrix_symm


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
    (cayleyMenger D).det = -16 * (triangleArea x) ^ 2 := by
  rw [cayleyMenger_det_triangle_centeredGram D (hD.hollow 0) (hD.hollow 1) (hD.hollow 2)
        (hD.symm 1 0) (hD.symm 2 0) (hD.symm 2 1),
      det_centeredGram_block_eq_sq hD, triangleArea]
  rw [div_pow, sq_abs]
  ring
end DistanceGeometry
