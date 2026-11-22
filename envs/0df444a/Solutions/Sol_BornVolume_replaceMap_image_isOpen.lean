-- Prove2me | solution 1 for BornVolume.replaceMap_image_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:00.533253+00:00
-- url     : https://prove2.me/submissions/71ce7eb7-0cf7-4f58-8b98-16f3c3cfa97f

module
public import Definitions.Def_BornVolumeLean_Volume_CellMeasurePos
public import Definitions.Def_BornVolumeLean_Volume_CellOpen
public import Theorems.Thm_BornVolume_isOpen_openSimplexFree


set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution (b : Fin M → ℝ) (i : Fin M)
    (h : LinearMap.det (replaceMap b i) ≠ 0) :
    IsOpen ((replaceMap b i) '' openSimplexFree) :=
  LinearMap.isOpenMap_of_finiteDimensional _
    (LinearMap.equivOfDetNeZero (replaceMap b i) h).surjective _ isOpen_openSimplexFree
end BornVolume
