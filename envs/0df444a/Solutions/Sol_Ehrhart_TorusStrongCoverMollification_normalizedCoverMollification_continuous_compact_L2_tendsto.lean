-- Prove2me | solution 1 for Ehrhart.TorusStrongCoverMollification.normalizedCoverMollification_continuous_compact_L2_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/242f1a6d-9277-4409-a1fe-2934b365300f

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerCoreApproximation_complexLp_norm_sq_eq_integral
import Theorems.Thm_Ehrhart_TorusStrongCoverMollification_tendsto_integral_norm_sq_normalizedCoverMollification_sub_of_continuous_compact

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusStrongCoverMollification
open Set Function Filter MeasureTheory
open TorusCharacters MatrixTorusBochnerCoreApproximation TorusWeakDolbeaultMollification
open TorusMollificationLocalL2Bounds TorusCompactTestGreen
open scoped ENNReal Topology ContDiff Convolution
namespace Ehrhart.TorusStrongCoverMollification
theorem _root_.solution
    {n : ℕ} {h : LogSpace n → ℂ}
    (hc : Continuous h) (hs : HasCompactSupport h) :
    Tendsto
      (fun k : ℕ =>
        (normalizedCoverMollification_memLp
          (hc.memLp_of_hasCompactSupport hs) k).toLp
            (normalizedCoverMollification h k))
      atTop
      (nhds
        ((hc.memLp_of_hasCompactSupport hs).toLp h)) := by
  let hh : MemLp h 2 (volume : Measure (LogSpace n)) :=
    hc.memLp_of_hasCompactSupport hs
  change Tendsto
    (fun k : ℕ =>
      (normalizedCoverMollification_memLp hh k).toLp
        (normalizedCoverMollification h k))
    atTop (nhds (hh.toLp h))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
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
      with x hsub hmoll hx
    rw [hsub]
    change
      ‖((normalizedCoverMollification_memLp hh k).toLp
          (normalizedCoverMollification h k)) x -
        (hh.toLp h) x‖ ^ 2 = _
    rw [hmoll, hx]
  have hsqtendsto :
      Tendsto
        (fun k : ℕ =>
          ‖(normalizedCoverMollification_memLp hh k).toLp
              (normalizedCoverMollification h k) -
            hh.toLp h‖ ^ 2)
        atTop (nhds 0) := by
    simpa only [hsq] using
      tendsto_integral_norm_sq_normalizedCoverMollification_sub_of_continuous_compact
        hc hs
  have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp
    hsqtendsto
  simpa [Function.comp_def, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (norm_nonneg _)] using hsqrt
end Ehrhart.TorusStrongCoverMollification
