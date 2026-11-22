-- Prove2me | solution 1 for BornVolume.apexMap_image_measurableSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:15.866806+00:00
-- url     : https://prove2.me/submissions/d646557d-645a-48ea-bc99-dd90a4ae8e98

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
theorem _root_.solution (b : Fin M → ℝ) :
    MeasurableSet ((fun x => apexLin b x + b) '' openSimplexFree) :=
  image_openSimplexFree_measurableSet
    ((apexLin b).continuous_of_finiteDimensional.add continuous_const)
end BornVolume
