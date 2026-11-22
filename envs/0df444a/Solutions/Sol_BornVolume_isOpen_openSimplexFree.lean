-- Prove2me | solution 1 for BornVolume.isOpen_openSimplexFree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:04:13.016808+00:00
-- url     : https://prove2.me/submissions/680980cc-c36c-4c42-b1b6-f9ccbdeebed0

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
theorem _root_.solution {M : ℕ} : IsOpen (openSimplexFree (M := M)) := by
  rw [openSimplexFree, Set.ofPred_and]
  refine IsOpen.inter ?_ ?_
  · rw [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun k => isOpen_lt continuous_const (continuous_apply k)
  · exact isOpen_lt (continuous_finsetSum _ fun k _ => continuous_apply k) continuous_const
end BornVolume
