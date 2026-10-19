-- Prove2me | solution 1 for Ehrhart.TorusStrongCoverMollification.normalizedCoverMollification_L2_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/75abfd11-7cb1-4725-b7a9-06734689f62c

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerCoreApproximation_complexLp_norm_sq_eq_integral
import Theorems.Thm_Ehrhart_TorusMollificationLocalL2Bounds_integral_norm_sq_normalizedCoverMollification_le

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
    (hh : MemLp h 2 (volume : Measure (LogSpace n)))
    (k : ℕ) :
    ‖(normalizedCoverMollification_memLp hh k).toLp
      (normalizedCoverMollification h k)‖ ≤
    ‖hh.toLp h‖ := by
  have hsq :
      ‖(normalizedCoverMollification_memLp hh k).toLp
        (normalizedCoverMollification h k)‖ ^ 2 ≤
      ‖hh.toLp h‖ ^ 2 := by
    calc
      ‖(normalizedCoverMollification_memLp hh k).toLp
        (normalizedCoverMollification h k)‖ ^ 2 =
        ∫ x : LogSpace n,
          ‖normalizedCoverMollification h k x‖ ^ 2
          ∂(volume : Measure (LogSpace n)) := by
            rw [complexLp_norm_sq_eq_integral]
            apply integral_congr_ae
            filter_upwards
              [(normalizedCoverMollification_memLp hh k).coeFn_toLp]
              with x hx
            rw [hx]
      _ ≤ ∫ x : LogSpace n, ‖h x‖ ^ 2
          ∂(volume : Measure (LogSpace n)) :=
            integral_norm_sq_normalizedCoverMollification_le hh k
      _ = ‖hh.toLp h‖ ^ 2 := by
            rw [complexLp_norm_sq_eq_integral]
            apply integral_congr_ae
            filter_upwards [hh.coeFn_toLp] with x hx
            rw [hx]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
end Ehrhart.TorusStrongCoverMollification
