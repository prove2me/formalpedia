-- Prove2me | solution 1 for Ehrhart.TorusStrongCoverMollificationDensity.tendsto_integral_norm_sq_normalizedCoverMollification_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/b6c3914b-fb4e-4060-9754-e6d5587e97e8

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerCoreApproximation_complexLp_norm_sq_eq_integral
import Theorems.Thm_Ehrhart_TorusStrongCoverMollificationDensity_normalizedCoverMollification_global_L2_tendsto

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
    {n : ℕ} {h : LogSpace n → ℂ}
    (hh : MemLp h 2 (volume : Measure (LogSpace n))) :
    Tendsto
      (fun k : ℕ =>
        ∫ x : LogSpace n,
          ‖normalizedCoverMollification h k x - h x‖ ^ 2
            ∂(volume : Measure (LogSpace n)))
      atTop (nhds 0) := by
  have hnorm := tendsto_iff_norm_sub_tendsto_zero.mp
    (normalizedCoverMollification_global_L2_tendsto hh)
  have hsq (k : ℕ) :
      ‖(normalizedCoverMollification_memLp hh k).toLp
          (normalizedCoverMollification h k) -
        hh.toLp h‖ ^ 2 =
      ∫ x : LogSpace n,
        ‖normalizedCoverMollification h k x - h x‖ ^ 2
          ∂(volume : Measure (LogSpace n)) := by
    rw [complexLp_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards
      [MeasureTheory.Lp.coeFn_sub
        ((normalizedCoverMollification_memLp hh k).toLp
          (normalizedCoverMollification h k)) (hh.toLp h),
       (normalizedCoverMollification_memLp hh k).coeFn_toLp,
       hh.coeFn_toLp]
      with x hsub hm hx
    rw [hsub]
    change
      ‖((normalizedCoverMollification_memLp hh k).toLp
          (normalizedCoverMollification h k)) x -
        (hh.toLp h) x‖ ^ 2 = _
    rw [hm, hx]
  simpa only [hsq, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
    hnorm.pow 2
end Ehrhart.TorusStrongCoverMollificationDensity
