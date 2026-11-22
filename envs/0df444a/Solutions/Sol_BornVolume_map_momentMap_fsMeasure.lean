-- Prove2me | solution 1 for BornVolume.map_momentMap_fsMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:35.870464+00:00
-- url     : https://prove2.me/submissions/abfe2343-e852-4688-8f4c-4e5cf9150330

module
public import Definitions.Def_BornVolumeLean_Volume_MomentDirichletN
public import Definitions.Def_BornVolumeLean_Volume_CellMeasure
public import Definitions.Def_BornVolumeLean_Volume_BornWeight
public import Theorems.Thm_BornVolume_freeMoment_eq_ratioN
public import Theorems.Thm_BornVolume_map_ratioN_momentMap_fsMeasure


set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup Projectivization
open scoped ENNReal
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution (p₀ : CPN (M + 1)) :
    Measure.map (fun (p : CPN (M + 1)) (k : Fin M) => momentMap p (Fin.castSucc k))
        (fsMeasure p₀)
      = (Nat.factorial M : ℝ≥0∞) • volume.restrict openSimplexFree := by
  rw [freeMoment_eq_ratioN]
  exact map_ratioN_momentMap_fsMeasure p₀
end BornVolume
