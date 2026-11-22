-- Prove2me | solution 1 for BornVolume.apexLin_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:04:33.614622+00:00
-- url     : https://prove2.me/submissions/70ce4599-8ddc-488c-b403-ea61d64b52c0

module
public import Definitions.Def_BornVolumeLean_Volume_MomentDirichletN
public import Definitions.Def_BornVolumeLean_Volume_VertexReplacement
public import Definitions.Def_BornVolumeLean_Volume_CellMeasurePos

set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution (b : Fin M → ℝ) (x : Fin M → ℝ) (k : Fin M) :
    (apexLin b) x k = x k - (∑ j, x j) * b k := by
  rw [apexLin, Matrix.toLin'_apply]
  show ((1 - Matrix.of (fun (k : Fin M) (_ : Fin M) => b k)) *ᵥ x) k = _
  rw [Matrix.sub_mulVec, Pi.sub_apply, Matrix.one_mulVec]
  congr 1
  simp only [Matrix.mulVec, Matrix.of_apply, dotProduct, ← Finset.mul_sum, mul_comm]
end BornVolume
