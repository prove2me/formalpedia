-- Prove2me | solution 1 for BornVolume.ratioN_momentMap_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:05:52.336538+00:00
-- url     : https://prove2.me/submissions/b6a9a788-01e0-4af0-8429-a072cc86cc00

module
public import Definitions.Def_BornVolumeLean_Volume_CellMeasurePos
public import Definitions.Def_BornVolumeLean_Volume_CellOpen
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
    (hψ : ‖ψ‖ = 1) (k : Fin M) :
    ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j) k
      = ‖inner ℂ (EuclideanSpace.single (Fin.castSucc k) (1 : ℂ)) ψ‖ ^ 2 := by
  simp only [ratioN]
  rw [show (∑ j, momentMap (Projectivization.mk ℂ ψ hψ0) j) = 1 from momentMap_sum_eq_one _,
    div_one, momentMap_mk_eq_inner_sq ψ hψ0 hψ (Fin.castSucc k)]
end BornVolume
