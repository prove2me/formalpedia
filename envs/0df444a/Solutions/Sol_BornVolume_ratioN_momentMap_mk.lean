-- Prove2me | solution 1 for BornVolume.ratioN_momentMap_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:06:53.616043+00:00
-- url     : https://prove2.me/submissions/207fbeb3-e395-494a-a237-28b705a732b8

module
public import Definitions.Def_BornVolumeLean_Volume_MomentDirichletN
public import Definitions.Def_BornVolumeLean_Volume_CellMeasure
public import Definitions.Def_BornVolumeLean_Volume_BornWeight
public import Theorems.Thm_BornVolume_ratioN_momentMap_castSucc


set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup Projectivization
open scoped ENNReal
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution (ψ : EuclideanSpace ℂ (Fin (M + 1))) (hψ0 : ψ ≠ 0) (hψ : ‖ψ‖ = 1) :
    ratioN (fun j => momentMap (Projectivization.mk ℂ ψ hψ0) j)
      = fun k => ‖ψ (Fin.castSucc k)‖ ^ 2 := by
  funext k
  rw [ratioN_momentMap_castSucc ψ hψ0 hψ k, EuclideanSpace.inner_single_left, map_one, one_mul]
end BornVolume
