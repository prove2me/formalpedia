-- Prove2me | solution 1 for BornVolume.measurableSet_bornCell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:10:31.80296+00:00
-- url     : https://prove2.me/submissions/480bc784-baed-4bc4-9894-2adbf509bc62

module
public import Definitions.Def_BornVolumeLean_Volume_BornWeight
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.IdentDistrib
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_BornVolumeLean_Volume_BornFrequency
public import Theorems.Thm_BornVolume_measurable_freeMoment
public import Theorems.Thm_BornVolume_apexMap_image_measurableSet
public import Theorems.Thm_BornVolume_replaceMap_image_measurableSet


set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory ProbabilityTheory Set Filter Matrix Matrix.UnitaryGroup Projectivization
open scoped ENNReal
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution (ψ : EuclideanSpace ℂ (Fin (M + 1))) (i : Fin (M + 1)) :
    MeasurableSet (bornCell ψ i) := by
  induction i using Fin.lastCases with
  | last =>
    rw [bornCell, Fin.lastCases_last]
    exact measurable_freeMoment (apexMap_image_measurableSet _)
  | cast k =>
    rw [bornCell, Fin.lastCases_castSucc]
    exact measurable_freeMoment (replaceMap_image_measurableSet _ k)
end BornVolume
