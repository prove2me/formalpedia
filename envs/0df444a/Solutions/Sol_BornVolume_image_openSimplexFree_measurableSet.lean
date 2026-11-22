-- Prove2me | solution 1 for BornVolume.image_openSimplexFree_measurableSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:08:08.755793+00:00
-- url     : https://prove2.me/submissions/d66484ed-babe-4b2b-bf36-daa370f77126

module
public import Definitions.Def_BornVolumeLean_Volume_CellOpen
public import Definitions.Def_BornVolumeLean_Volume_CellMeasure
public import Theorems.Thm_BornVolume_isSigmaCompact_openSimplexFree

set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution {f : (Fin M → ℝ) → (Fin M → ℝ)}
    (hf : Continuous f) : MeasurableSet (f '' openSimplexFree) := by
  obtain ⟨K, hK, hKeq⟩ := isSigmaCompact_openSimplexFree.image hf
  rw [← hKeq]
  exact MeasurableSet.iUnion fun n => (hK n).isClosed.measurableSet
end BornVolume
