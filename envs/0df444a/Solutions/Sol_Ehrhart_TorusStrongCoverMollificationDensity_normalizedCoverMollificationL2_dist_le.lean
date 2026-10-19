-- Prove2me | solution 1 for Ehrhart.TorusStrongCoverMollificationDensity.normalizedCoverMollificationL2_dist_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/163789dc-674b-49da-be1d-d4fe807c2526

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusStrongCoverMollification_normalizedCoverMollification_L2_norm_le
import Theorems.Thm_Ehrhart_TorusStrongCoverMollificationDensity_normalizedCoverMollificationL2_sub

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
    dist (normalizedCoverMollificationL2 k u)
      (normalizedCoverMollificationL2 k v) ≤ dist u v := by
  rw [dist_eq_norm, normalizedCoverMollificationL2_sub]
  let hmem : MemLp (fun x : LogSpace n => u x - v x)
      2 (volume : Measure (LogSpace n)) :=
    (MeasureTheory.Lp.memLp u).sub (MeasureTheory.Lp.memLp v)
  have hc := normalizedCoverMollification_L2_norm_le hmem k
  rw [dist_eq_norm]
  calc
    _ ≤ ‖hmem.toLp
          (fun x : LogSpace n => u x - v x)‖ := hc
    _ = ‖u - v‖ := by
      congr 1
      apply MeasureTheory.Lp.ext
      filter_upwards
        [hmem.coeFn_toLp,
         MeasureTheory.Lp.coeFn_sub u v] with x hx hsub
      rw [hx, hsub]
      rfl
end Ehrhart.TorusStrongCoverMollificationDensity
