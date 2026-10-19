-- Prove2me | solution 1 for Ehrhart.TorusStrongCoverMollificationDensity.normalizedCoverMollification_localL2_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/bb29eb62-3681-4ee9-aa99-b5d4ed62ba6d

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusStrongCoverMollificationDensity_tendsto_integral_norm_sq_normalizedCoverMollification_sub
import Theorems.Thm_Ehrhart_TorusStrongCoverMollificationDensity_normalizedCoverMollification_indicator_cthickening_eq_on

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
    (_ : LocallyIntegrable h (volume : Measure (LogSpace n)))
    {K : Set (LogSpace n)} (hK : IsCompact K)
    (hlocal : MemLp h 2
      ((volume : Measure (LogSpace n)).restrict
        (Metric.cthickening 1 K))) :
    Tendsto
      (fun k : ℕ =>
        ∫ x in K,
          ‖normalizedCoverMollification h k x - h x‖ ^ 2
            ∂(volume : Measure (LogSpace n)))
      atTop (nhds 0) := by
  let S : Set (LogSpace n) := Metric.cthickening 1 K
  let z : LogSpace n → ℂ := S.indicator h
  have hS : IsCompact S := hK.cthickening
  have hz : MemLp z 2 (volume : Measure (LogSpace n)) :=
    (MeasureTheory.memLp_indicator_iff_restrict
      hS.measurableSet).mpr hlocal
  have hagree (k : ℕ) :
      (∫ x in K,
        ‖normalizedCoverMollification h k x - h x‖ ^ 2
          ∂(volume : Measure (LogSpace n))) =
      (∫ x in K,
        ‖normalizedCoverMollification z k x - z x‖ ^ 2
          ∂(volume : Measure (LogSpace n))) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    have hxs : x ∈ S := Metric.self_subset_cthickening K hx
    change
      ‖normalizedCoverMollification h k x - h x‖ ^ 2 =
        ‖normalizedCoverMollification
          ((Metric.cthickening 1 K).indicator h) k x -
          (Metric.cthickening 1 K).indicator h x‖ ^ 2
    rw [normalizedCoverMollification_indicator_cthickening_eq_on
      hK k x hx, Set.indicator_of_mem hxs]
  have hbound (k : ℕ) :
      (∫ x in K,
        ‖normalizedCoverMollification h k x - h x‖ ^ 2
          ∂(volume : Measure (LogSpace n))) ≤
      (∫ x : LogSpace n,
        ‖normalizedCoverMollification z k x - z x‖ ^ 2
          ∂(volume : Measure (LogSpace n))) := by
    rw [hagree k]
    apply MeasureTheory.setIntegral_le_integral
      ((normalizedCoverMollification_memLp hz k).sub hz).norm.integrable_sq
    exact Filter.Eventually.of_forall (fun x => sq_nonneg _)
  exact squeeze_zero
    (fun k => integral_nonneg (fun x => sq_nonneg _))
    hbound
    (tendsto_integral_norm_sq_normalizedCoverMollification_sub hz)
end Ehrhart.TorusStrongCoverMollificationDensity
