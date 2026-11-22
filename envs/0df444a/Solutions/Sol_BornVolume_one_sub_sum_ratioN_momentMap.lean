-- Prove2me | solution 1 for BornVolume.one_sub_sum_ratioN_momentMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:06:50.932382+00:00
-- url     : https://prove2.me/submissions/395c1130-9ce2-488f-9edf-7e1d24279e93

module
public import Definitions.Def_BornVolumeLean_Volume_CellMeasurePos
public import Definitions.Def_BornVolumeLean_Volume_CellOpen
public import Theorems.Thm_BornVolume_ratioN_momentMap_castSucc
public import Theorems.Thm_Projectivization_momentMap_mk_eq_inner_sq
public import Theorems.Thm_Projectivization_momentMap_sum_eq_one


set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0)
    (hψ : ‖ψ‖ = 1) :
    (1 : ℝ) - ∑ k, ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j) k
      = ‖inner ℂ (EuclideanSpace.single (Fin.last M) (1 : ℂ)) ψ‖ ^ 2 := by
  have hsum1 : ∑ j, momentMap (Projectivization.mk ℂ ψ hψ0) j = 1 := momentMap_sum_eq_one _
  rw [Fin.sum_univ_castSucc] at hsum1
  have heq : ∑ k, ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j) k
      = ∑ k : Fin M, momentMap (Projectivization.mk ℂ ψ hψ0) (Fin.castSucc k) :=
    Finset.sum_congr rfl (fun k _ => by
      rw [ratioN_momentMap_castSucc ψ hψ0 hψ k, momentMap_mk_eq_inner_sq ψ hψ0 hψ (Fin.castSucc k)])
  rw [heq, momentMap_mk_eq_inner_sq ψ hψ0 hψ (Fin.last M)] at *
  linarith
end BornVolume
