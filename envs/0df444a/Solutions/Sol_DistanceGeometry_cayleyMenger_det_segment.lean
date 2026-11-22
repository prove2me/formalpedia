-- Prove2me | solution 1 for DistanceGeometry.cayleyMenger_det_segment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:46:51.432215+00:00
-- url     : https://prove2.me/submissions/0fd0518e-c07d-4ce5-b5ea-3c66b9adbe8d

module
public import Definitions.Def_LeanPool_DistanceGeometry_Defs
public import Definitions.Def_LeanPool_DistanceGeometry_Schoenberg
public import Definitions.Def_LeanPool_DistanceGeometry_CayleyMengerVolume
public import Theorems.Thm_DistanceGeometry_cayleyMenger_zero_zero
public import Theorems.Thm_DistanceGeometry_cayleyMenger_zero_succ
public import Theorems.Thm_DistanceGeometry_cayleyMenger_succ_zero
public import Theorems.Thm_DistanceGeometry_cayleyMenger_succ_succ
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
theorem _root_.solution (D : Matrix (Fin 2) (Fin 2) ℝ)
    (h00 : D 0 0 = 0) (h11 : D 1 1 = 0) (s01 : D 1 0 = D 0 1) :
    (cayleyMenger D).det = 2 * D 0 1 := by
  rw [det_fin_three]
  simp only [show cayleyMenger D 0 0 = 0 from rfl, show cayleyMenger D 0 1 = 1 from rfl,
      show cayleyMenger D 0 2 = 1 from rfl, show cayleyMenger D 1 0 = 1 from rfl,
      show cayleyMenger D 1 1 = D 0 0 from rfl, show cayleyMenger D 1 2 = D 0 1 from rfl,
      show cayleyMenger D 2 0 = 1 from rfl, show cayleyMenger D 2 1 = D 1 0 from rfl,
      show cayleyMenger D 2 2 = D 1 1 from rfl, h00, h11, s01]
  ring
end DistanceGeometry
