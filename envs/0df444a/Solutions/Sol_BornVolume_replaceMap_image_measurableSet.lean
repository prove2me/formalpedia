-- Prove2me | solution 1 for BornVolume.replaceMap_image_measurableSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:15.458742+00:00
-- url     : https://prove2.me/submissions/8cc7bd70-1167-4a97-b539-e92cdf84df45

module
public import Definitions.Def_BornVolumeLean_Volume_CellOpen
public import Definitions.Def_BornVolumeLean_Volume_CellMeasure
public import Theorems.Thm_BornVolume_image_openSimplexFree_measurableSet

set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution (b : Fin M → ℝ) (i : Fin M) :
    MeasurableSet ((replaceMap b i) '' openSimplexFree) :=
  image_openSimplexFree_measurableSet (replaceMap b i).continuous_of_finiteDimensional
end BornVolume
