-- Prove2me | solution 1 for BornVolume.freeMoment_eq_ratioN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:06:45.465799+00:00
-- url     : https://prove2.me/submissions/72ab39c0-c644-4328-9592-57255599377c

module
public import Definitions.Def_BornVolumeLean_Volume_MomentDirichletN
public import Definitions.Def_BornVolumeLean_Volume_CellMeasure
public import Definitions.Def_BornVolumeLean_Volume_BornWeight
public import Theorems.Thm_Projectivization_momentMap_sum_eq_one


set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup Projectivization
open scoped ENNReal
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution :
    (fun (p : CPN (M + 1)) (k : Fin M) => momentMap p (Fin.castSucc k))
      = fun p : CPN (M + 1) => ratioN (fun i => momentMap p i) := by
  funext p k
  simp [ratioN, momentMap_sum_eq_one]
end BornVolume
