-- Prove2me | solution 1 for BornVolume.apexLin_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:04:13.829649+00:00
-- url     : https://prove2.me/submissions/ec122721-1905-4142-b154-2cf60cc63231

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
theorem _root_.solution (b : Fin M → ℝ) : LinearMap.det (apexLin b) = 1 - ∑ k, b k := by
  rw [apexLin, LinearMap.det_toLin']
  rw [show (Matrix.of (fun (k : Fin M) (_ : Fin M) => b k))
        = (Matrix.of (fun (k : Fin M) (_ : Fin 1) => b k))
          * (Matrix.of (fun (_ : Fin 1) (_ : Fin M) => (1 : ℝ))) from by
      ext k j; simp [Matrix.mul_apply]]
  rw [Matrix.det_one_sub_mul_comm, Matrix.det_fin_one]
  simp [Matrix.mul_apply, Matrix.sub_apply]
end BornVolume
