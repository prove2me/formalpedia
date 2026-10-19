-- Prove2me | solution 1 for Ehrhart.TorusStrongCoverMollificationDensity.normalizedCoverMollificationL2_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/742fa6af-4bbd-4e63-aaa4-a11dfc9c1f01

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusStrongCoverMollificationDensity_normalizedCoverMollification_sub

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusStrongCoverMollificationDensity
open Set Function Filter MeasureTheory Matrix
open TorusCharacters DolbeaultRegularity MatrixTorusBochnerCoreApproximation
open TorusWeakDolbeaultMollification TorusMollificationLocalL2Bounds TorusStrongCoverMollification
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusStrongCoverMollificationDensity
theorem _root_.solution
    {n : ℕ} (k : ℕ)
    (u v : MeasureTheory.Lp ℂ 2 (volume : Measure (LogSpace n))) :
    normalizedCoverMollificationL2 k u -
      normalizedCoverMollificationL2 k v =
    (normalizedCoverMollification_memLp
      ((MeasureTheory.Lp.memLp u).sub (MeasureTheory.Lp.memLp v)) k).toLp
      (normalizedCoverMollification
        (fun x : LogSpace n => u x - v x) k) := by
  let hmem : MemLp (fun x : LogSpace n => u x - v x)
      2 (volume : Measure (LogSpace n)) :=
    (MeasureTheory.Lp.memLp u).sub (MeasureTheory.Lp.memLp v)
  change
    normalizedCoverMollificationL2 k u -
      normalizedCoverMollificationL2 k v =
      (normalizedCoverMollification_memLp hmem k).toLp
        (normalizedCoverMollification
          (fun x : LogSpace n => u x - v x) k)
  apply MeasureTheory.Lp.ext
  filter_upwards
    [MeasureTheory.Lp.coeFn_sub
      (normalizedCoverMollificationL2 k u)
      (normalizedCoverMollificationL2 k v),
     (normalizedCoverMollification_memLp
       (MeasureTheory.Lp.memLp u) k).coeFn_toLp,
     (normalizedCoverMollification_memLp
       (MeasureTheory.Lp.memLp v) k).coeFn_toLp,
     (normalizedCoverMollification_memLp hmem k).coeFn_toLp]
    with x hsub hu hv hdiff
  rw [hsub]
  change
    (normalizedCoverMollificationL2 k u) x -
      (normalizedCoverMollificationL2 k v) x = _
  change
    ((normalizedCoverMollification_memLp
        (MeasureTheory.Lp.memLp u) k).toLp
      (normalizedCoverMollification (fun x : LogSpace n => u x) k)) x -
    ((normalizedCoverMollification_memLp
        (MeasureTheory.Lp.memLp v) k).toLp
      (normalizedCoverMollification (fun x : LogSpace n => v x) k)) x = _
  rw [hu, hv, hdiff,
    normalizedCoverMollification_sub
      (MeasureTheory.Lp.memLp u) (MeasureTheory.Lp.memLp v) k x]
end Ehrhart.TorusStrongCoverMollificationDensity
