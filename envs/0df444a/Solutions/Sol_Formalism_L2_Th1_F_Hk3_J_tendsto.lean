-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk3.J_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:48:22.854926+00:00
-- url     : https://prove2.me/submissions/12834a8d-2fc2-42c6-a76e-ab6b0d2b7fc1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelLineZero
import Theorems.Thm_Formalism_L2_Th1_F_Hk3_one_add_sq_pos
import Theorems.Thm_Formalism_L2_Th1_F_Hk3_J_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.Hk3
namespace Formalism.L2.Th1.F.Hk3
theorem _root_.solution : Tendsto (fun s : ℝ => hkJ (1 + s)) (𝓝[>] 0) (𝓝 Real.pi) := by
  rw [← J_one]
  unfold hkJ
  refine tendsto_integral_filter_of_dominated_convergence (fun t : ℝ => (1 + t ^ 2)⁻¹) ?_ ?_
    integrable_inv_one_add_sq ?_
  · exact Eventually.of_forall fun s => Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    refine Eventually.of_forall fun t => ?_
    have hp := one_add_sq_pos t
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hp.le _), ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg t]) (by
      have : (0 : ℝ) < s := hs
      linarith)
  · refine Eventually.of_forall fun t => ?_
    have hp := one_add_sq_pos t
    have hc : Continuous (fun s : ℝ => (1 + t ^ 2) ^ (-(1 + s))) :=
      Continuous.rpow continuous_const (by fun_prop) (fun _ => Or.inl hp.ne')
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
end Formalism.L2.Th1.F.Hk3
