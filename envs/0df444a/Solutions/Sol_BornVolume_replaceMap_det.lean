-- Prove2me | solution 1 for BornVolume.replaceMap_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:58:58.597953+00:00
-- url     : https://prove2.me/submissions/65c5af58-2667-4465-8c83-6b097dc4e676

module
public import Definitions.Def_BornVolumeLean_Volume_MomentMap
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Definitions.Def_BornVolumeLean_Volume_VertexReplacement

set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Matrix
open scoped LinearAlgebra.Projectivization
open BornVolume
variable {N : ℕ}
namespace BornVolume
theorem _root_.solution (b : Fin N → ℝ) (i : Fin N) :
    LinearMap.det (replaceMap b i) = b i := by
  rw [replaceMap, LinearMap.det_toLin', ← Matrix.cramer_apply, Matrix.cramer_one]
  rfl
end BornVolume
