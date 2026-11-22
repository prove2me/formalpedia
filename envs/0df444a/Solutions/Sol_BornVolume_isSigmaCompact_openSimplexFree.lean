-- Prove2me | solution 1 for BornVolume.isSigmaCompact_openSimplexFree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:07:01.47348+00:00
-- url     : https://prove2.me/submissions/83dee751-5cce-4320-a2ad-f4e40eba5c1b

module
public import Definitions.Def_BornVolumeLean_Volume_CellOpen
public import Definitions.Def_BornVolumeLean_Volume_CellMeasure
public import Theorems.Thm_BornVolume_isOpen_openSimplexFree


set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution :
    IsSigmaCompact (openSimplexFree (M := M)) := by
  have : LocallyCompactSpace (openSimplexFree (M := M)) :=
    (isOpen_openSimplexFree (M := M)).locallyCompactSpace
  exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
end BornVolume
