-- Prove2me | solution 1 for BornVolume.replaceMap_image_volume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:59:54.944052+00:00
-- url     : https://prove2.me/submissions/5b04268f-bea4-4792-a545-ffea429090ab

module
public import Definitions.Def_BornVolumeLean_Volume_MomentMap
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Definitions.Def_BornVolumeLean_Volume_VertexReplacement
public import Theorems.Thm_BornVolume_replaceMap_det

set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Matrix
open scoped LinearAlgebra.Projectivization
open BornVolume
variable {N : ℕ}
namespace BornVolume
theorem _root_.solution (b : Fin N → ℝ) (i : Fin N) (hb : 0 ≤ b i)
    (s : Set (Fin N → ℝ)) :
    volume (replaceMap b i '' s) = ENNReal.ofReal (b i) * volume s := by
  rw [Measure.addHaar_image_linearMap volume (replaceMap b i) s, replaceMap_det,
      abs_of_nonneg hb]
end BornVolume
