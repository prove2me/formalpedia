-- Prove2me | solution 1 for DistanceGeometry.cayleyMenger_det_triangle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:46:50.81336+00:00
-- url     : https://prove2.me/submissions/561f9b87-0ef8-4e71-bc35-e9976fb74439

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
section
@[expose] public section
namespace DistanceGeometry
open Matrix
open scoped RealInnerProductSpace
variable {n : ℕ}
private theorem det_fin_three_factored {R : Type*} [CommRing R]
    (M : Matrix (Fin 3) (Fin 3) R) :
    M.det = M 0 0 * (M 1 1 * M 2 2 - M 1 2 * M 2 1)
      - M 0 1 * (M 1 0 * M 2 2 - M 1 2 * M 2 0)
      + M 0 2 * (M 1 0 * M 2 1 - M 1 1 * M 2 0) := by
  rw [det_fin_three]
  ring
private theorem det_fin_four {R : Type*} [CommRing R] (M : Matrix (Fin 4) (Fin 4) R) :
    M.det =
      M 0 0 * (M 1 1 * (M 2 2 * M 3 3 - M 2 3 * M 3 2)
                - M 1 2 * (M 2 1 * M 3 3 - M 2 3 * M 3 1)
                + M 1 3 * (M 2 1 * M 3 2 - M 2 2 * M 3 1))
    - M 0 1 * (M 1 0 * (M 2 2 * M 3 3 - M 2 3 * M 3 2)
                - M 1 2 * (M 2 0 * M 3 3 - M 2 3 * M 3 0)
                + M 1 3 * (M 2 0 * M 3 2 - M 2 2 * M 3 0))
    + M 0 2 * (M 1 0 * (M 2 1 * M 3 3 - M 2 3 * M 3 1)
                - M 1 1 * (M 2 0 * M 3 3 - M 2 3 * M 3 0)
                + M 1 3 * (M 2 0 * M 3 1 - M 2 1 * M 3 0))
    - M 0 3 * (M 1 0 * (M 2 1 * M 3 2 - M 2 2 * M 3 1)
                - M 1 1 * (M 2 0 * M 3 2 - M 2 2 * M 3 0)
                + M 1 2 * (M 2 0 * M 3 1 - M 2 1 * M 3 0)) := by
  rw [det_succ_row_zero]
  simp only [Fin.sum_univ_four, det_fin_three_factored, submatrix_apply]
  norm_num [Fin.succAbove, Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.lt_def]
  simp only [sub_eq_add_neg]
  rfl
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
theorem _root_.solution (D : Matrix (Fin 3) (Fin 3) ℝ)
    (h00 : D 0 0 = 0) (h11 : D 1 1 = 0) (h22 : D 2 2 = 0)
    (s01 : D 1 0 = D 0 1) (s02 : D 2 0 = D 0 2) (s12 : D 2 1 = D 1 2) :
    (cayleyMenger D).det
      = -4 * (D 0 1 * D 0 2 - ((D 0 1 + D 0 2 - D 1 2) / 2) ^ 2) := by
  rw [det_fin_four]
  simp only [show cayleyMenger D 0 0 = 0 from rfl, show cayleyMenger D 0 1 = 1 from rfl,
      show cayleyMenger D 0 2 = 1 from rfl, show cayleyMenger D 0 3 = 1 from rfl,
      show cayleyMenger D 1 0 = 1 from rfl, show cayleyMenger D 1 1 = D 0 0 from rfl,
      show cayleyMenger D 1 2 = D 0 1 from rfl, show cayleyMenger D 1 3 = D 0 2 from rfl,
      show cayleyMenger D 2 0 = 1 from rfl, show cayleyMenger D 2 1 = D 1 0 from rfl,
      show cayleyMenger D 2 2 = D 1 1 from rfl, show cayleyMenger D 2 3 = D 1 2 from rfl,
      show cayleyMenger D 3 0 = 1 from rfl, show cayleyMenger D 3 1 = D 2 0 from rfl,
      show cayleyMenger D 3 2 = D 2 1 from rfl, show cayleyMenger D 3 3 = D 2 2 from rfl,
      h00, h11, h22, s01, s02, s12]
  ring
end DistanceGeometry
