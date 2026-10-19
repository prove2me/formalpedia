-- Prove2me | solution 1 for Ehrhart.TorusStrongCoverMollification.tendsto_integral_norm_sq_normalizedCoverMollification_sub_of_continuous_compact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/5c1b4f1f-aeab-4bd1-aeea-49867be5a994

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusCompactTestGreen_normalizedCoverMollification_tendsto_of_continuous
import Theorems.Thm_Ehrhart_TorusCompactTestGreen_tsupport_normalizedCoverMollification_subset_cthickening
import Theorems.Thm_Ehrhart_TorusCompactTestGreen_norm_normalizedCoverMollification_le_of_continuous_bound

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
        ∫ x : LogSpace n,
          ‖normalizedCoverMollification h k x - h x‖ ^ 2
            ∂(volume : Measure (LogSpace n)))
      atTop (nhds 0) := by
  obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support hs
  have hB₀ : 0 ≤ B := (norm_nonneg (h 0)).trans (hB 0)
  let S : Set (LogSpace n) := Metric.cthickening 1 (tsupport h)
  have hS : IsCompact S := hs.cthickening
  have hsubset : tsupport h ⊆ S := by
    intro x hx
    apply Metric.mem_cthickening_of_dist_le x x 1 (tsupport h) hx
    simp
  have hdom : Integrable
      (S.indicator
        (fun _ : LogSpace n => (2 * B) ^ 2))
      (volume : Measure (LogSpace n)) := by
    apply IntegrableOn.integrable_indicator _ hS.measurableSet
    exact continuous_const.continuousOn.integrableOn_compact hS
  have hconv := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure (LogSpace n)))
    (F := fun k : ℕ => fun x : LogSpace n =>
      ‖normalizedCoverMollification h k x - h x‖ ^ 2)
    (f := fun _ : LogSpace n => (0 : ℝ))
    (S.indicator (fun _ : LogSpace n => (2 * B) ^ 2))
    (by
      intro k
      exact (((contDiff_normalizedCoverMollification
        hc.locallyIntegrable k 0).continuous.sub hc).norm.pow 2).aestronglyMeasurable)
    hdom
    (by
      intro k
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx]
        apply (sq_le_sq₀ (norm_nonneg _)
          (mul_nonneg (by norm_num) hB₀)).mpr
        calc
          ‖normalizedCoverMollification h k x - h x‖ ≤
              ‖normalizedCoverMollification h k x‖ + ‖h x‖ :=
                norm_sub_le _ _
          _ ≤ B + B := add_le_add
            (norm_normalizedCoverMollification_le_of_continuous_bound
              hc hB₀ hB k x) (hB x)
          _ = 2 * B := by ring
      · have hmx : normalizedCoverMollification h k x = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro hm
          exact hx
            (tsupport_normalizedCoverMollification_subset_cthickening
              k hm)
        have hhx : h x = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro hh
          exact hx (hsubset hh)
        simp [Set.indicator_of_notMem hx, hmx, hhx])
    (by
      filter_upwards [] with x
      have ht : Tendsto
          (fun k : ℕ =>
            normalizedCoverMollification h k x - h x)
          atTop (nhds (0 : ℂ)) := by
        simpa using
          (normalizedCoverMollification_tendsto_of_continuous
            hc x).sub (tendsto_const_nhds (x := h x))
      simpa using ht.norm.pow 2)
  simpa using hconv
end Ehrhart.TorusStrongCoverMollification
