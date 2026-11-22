-- Prove2me | solution 1 for BornVolume.measurable_ratio_momentMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:04:12.401661+00:00
-- url     : https://prove2.me/submissions/83f9e7f8-09ed-4109-b05a-aaeb5e9a3c3e

module
public import Definitions.Def_BornVolumeLean_Volume_MomentDirichletN
public import Definitions.Def_BornVolumeLean_Volume_VertexReplacement
public import Definitions.Def_BornVolumeLean_Volume_CellMeasurePos
public import Theorems.Thm_BornVolume_momentMap_measurable


set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution :
    Measurable (fun p : CPN (M + 1) => ratioN (fun i => momentMap p i)) := by
  have hmoment : Measurable (fun p : CPN (M + 1) => fun i => momentMap p i) :=
    measurable_pi_iff.mpr (fun i => momentMap_measurable i)
  have hratio : Measurable (ratioN (M := M)) :=
    measurable_pi_iff.mpr (fun k => (measurable_pi_apply _).div
      (Finset.measurable_sum Finset.univ (fun i _ => measurable_pi_apply i)))
  exact hratio.comp hmoment
end BornVolume
