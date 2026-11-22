-- Prove2me | solution 1 for DistanceGeometry.cayleyMenger_det_triangle_centeredGram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:47:37.63552+00:00
-- url     : https://prove2.me/submissions/ce62a9af-34f9-4501-a940-fd3183f3097e

module
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
public import Definitions.Def_LeanPool_DistanceGeometry_Schoenberg
public import Definitions.Def_LeanPool_DistanceGeometry_CayleyMengerVolume
public import Theorems.Thm_DistanceGeometry_cayleyMenger_zero_zero
public import Theorems.Thm_DistanceGeometry_cayleyMenger_zero_succ
public import Theorems.Thm_DistanceGeometry_cayleyMenger_succ_zero
public import Theorems.Thm_DistanceGeometry_cayleyMenger_succ_succ
public import Theorems.Thm_DistanceGeometry_cayleyMenger_det_triangle
public import Theorems.Thm_DistanceGeometry_centeredGram_apply
public import Theorems.Thm_DistanceGeometry_sqDistMatrix_apply
attribute [local simp] DistanceGeometry.centeredGram_apply
attribute [local simp] DistanceGeometry.sqDistMatrix_apply


attribute [local simp] DistanceGeometry.cayleyMenger_zero_zero
attribute [local simp] DistanceGeometry.cayleyMenger_zero_succ
attribute [local simp] DistanceGeometry.cayleyMenger_succ_zero
attribute [local simp] DistanceGeometry.cayleyMenger_succ_succ

set_option autoImplicit true
@[expose] public section
public section
open DistanceGeometry
open Matrix
open scoped RealInnerProductSpace
variable {n : ℕ}
namespace DistanceGeometry
theorem _root_.solution (D : Matrix (Fin 3) (Fin 3) ℝ)
    (h00 : D 0 0 = 0) (h11 : D 1 1 = 0) (h22 : D 2 2 = 0)
    (s01 : D 1 0 = D 0 1) (s02 : D 2 0 = D 0 2) (s12 : D 2 1 = D 1 2) :
    (cayleyMenger D).det
      = -4 * (centeredGram D 1 1 * centeredGram D 2 2 - (centeredGram D 1 2) ^ 2) := by
  rw [cayleyMenger_det_triangle D h00 h11 h22 s01 s02 s12]
  -- evaluate the three centeredGram entries on `Fin 3`
  have e11 : centeredGram D 1 1 = D 0 1 := by simp [centeredGram_apply, h11]
  have e22 : centeredGram D 2 2 = D 0 2 := by simp [centeredGram_apply, h22]
  have e12 : centeredGram D 1 2 = (D 0 1 + D 0 2 - D 1 2) / 2 := by simp [centeredGram_apply]
  rw [e11, e22, e12]
end DistanceGeometry
