-- Prove2me | solution 1 for Formalism.L2.Th1.F.Hk3.real_limit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:35:13.616109+00:00
-- url     : https://prove2.me/submissions/f9a8cba6-9680-4857-90b4-0dab2fb7a81e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_HkRowIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_HeckeKernelLineZero
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_mul
import Theorems.Thm_Formalism_G_LogCR_Agree_mul


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
theorem _root_.solution (hj : HkJRules) {y : ℝ} (hy : y ≠ 0) :
    Tendsto (fun s : ℝ => (((1 + 2 * s) - 1) * ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 2 * s)) *
        (|y| ^ (-(1 + 2 * s)) * (-(1 / (s + 1)) * hkJ (1 + s)))) (𝓝[>] 0)
      (𝓝 (-(Real.pi / |y|))) := by
  have hp : 0 < |y| := abs_pos.mpr hy
  have hm : Tendsto (fun s : ℝ => 1 + 2 * s) (𝓝[>] 0) (𝓝[>] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Continuous (fun s : ℝ => 1 + 2 * s) := by fun_prop
      simpa using (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_Ioi] at hs ⊢
      linarith
  have h2 := tendsto_sub_mul_tsum_nat_rpow.comp hm
  have h3 : Tendsto (fun s : ℝ => |y| ^ (-(1 + 2 * s))) (𝓝[>] 0) (𝓝 (|y|⁻¹)) := by
    have hc : Continuous (fun s : ℝ => |y| ^ (-(1 + 2 * s))) :=
      Continuous.rpow continuous_const (by fun_prop) (fun _ => Or.inl hp.ne')
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa [Real.rpow_neg_one] using this
  have h4 : Tendsto (fun s : ℝ => -(1 / (s + 1))) (𝓝[>] 0) (𝓝 (-1)) := by
    have hc : ContinuousAt (fun s : ℝ => -(1 / (s + 1))) 0 :=
      (ContinuousAt.div continuousAt_const (by fun_prop) (by norm_num)).neg
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  have h := h2.mul (h3.mul (h4.mul hj.2.2))
  have e : (1 : ℝ) * (|y|⁻¹ * (-1 * Real.pi)) = -(Real.pi / |y|) := by
    rw [div_eq_mul_inv]
    ring
  rw [e] at h
  exact h
end Formalism.L2.Th1.F.Hk3
