-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.herglotz_lower_semicontinuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:18:58.529913+00:00
-- url     : https://prove2.me/submissions/5e3436ab-ed7c-4cdb-920e-90861e643c1a

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_isCompact_cube
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_continuous_pk
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_pk_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_pk_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_pk_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_upper_pk
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_lower_pk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Real Filter Topology Finset MeasureTheory Formalism.FourierDecayAlt.P.Herglotz Formalism.FourierDecayAlt.P.HLsc
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.E.HerglotzLSC := by
  intro d N A hN0 hlsc hint hPD hsum z₀ S
  change Summable (fun σ : Fin d → ℤ => ‖(∫ z, (N z : ℂ) * ee z σ) + A σ‖) at hsum
  change _ ≤ ∑' σ : Fin d → ℤ, ‖(∫ z, (N z : ℂ) * ee z σ) + A σ‖
  set K := ∑' σ : Fin d → ℤ, ‖(∫ z, (N z : ℂ) * ee z σ) + A σ‖ with hK
  have hK0 : 0 ≤ K := tsum_nonneg (fun _ => norm_nonneg _)
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  set η : ℝ := ε / ((S.card : ℝ) + 1) with hη
  have hηpos : 0 < η := by positivity
  have hev : ∀ᶠ y in 𝓝 (0 : Fin d → ℝ), ∀ m ∈ S,
      N (fun j => z₀ j + (m j : ℝ)) - η < N (fun j => z₀ j + (m j : ℝ) + y j) := by
    rw [Filter.eventually_all_finset]
    intro m _
    have h1 := hlsc (fun j => z₀ j + (m j : ℝ)) (N (fun j => z₀ j + (m j : ℝ)) - η) (by linarith)
    have h2 : Tendsto (fun y : Fin d → ℝ => (fun j => z₀ j + (m j : ℝ) + y j)) (𝓝 0)
        (𝓝 (fun j => z₀ j + (m j : ℝ))) := by
      have hc : Continuous (fun y : Fin d → ℝ => (fun j => z₀ j + (m j : ℝ) + y j)) := by fun_prop
      exact hc.tendsto' _ _ (by simp)
    exact h2.eventually h1
  have hball : ∀ᶠ y in 𝓝 (0 : Fin d → ℝ), ∀ j, |y j| < 1 / 2 := by
    filter_upwards [Metric.ball_mem_nhds (0 : Fin d → ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with y hy j
    rw [mem_ball_zero_iff] at hy
    exact lt_of_le_of_lt (norm_le_pi_norm y j) hy
  obtain ⟨U, hUsub, hUo, h0U⟩ := mem_nhds_iff.1 (hev.and hball)
  have hT := tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_integrableOn
    (μ := (volume : Measure (Fin d → ℝ))) (x₀ := 0) (g := U.indicator (fun _ => (1 : ℝ)))
    isCompact_cube continuous_pk.continuousOn pk_lt (fun x _ => pk_nonneg x)
    (by rw [pk_zero]; positivity)
    (subset_closure (mem_interior_iff_mem_nhds.2
      (pi_Icc_mem_nhds (fun _ => by norm_num) (fun _ => by norm_num))))
    ((integrableOn_const (isCompact_cube.measure_lt_top.ne)).indicator hUo.measurableSet)
    (by
      have : U.indicator (fun _ => (1 : ℝ)) =ᶠ[𝓝 0] fun _ => (1 : ℝ) := by
        filter_upwards [hUo.mem_nhds h0U] with y hy
        exact Set.indicator_of_mem hy _
      exact (continuousAt_const.congr this.symm).continuousWithinAt)
  rw [Set.indicator_of_mem h0U] at hT
  have hle : ∀ n : ℕ, (∑ m ∈ S, (N (fun j => z₀ j + (m j : ℝ)) - η)) *
      ((∫ x in cube d, pk x ^ n)⁻¹ • ∫ x in cube d, pk x ^ n • U.indicator (fun _ => (1 : ℝ)) x) ≤ K := by
    intro n
    have h1 := (lower_pk hN0 hint z₀ S η U hUo (fun y hy => (hUsub hy).1) (fun y hy => (hUsub hy).2) n).trans
      (upper_pk hint hPD hsum z₀ n)
    have hI : 0 ≤ ∫ x in cube d, pk x ^ n := integral_nonneg (fun x => pow_nonneg (pk_nonneg x) n)
    have h2 := mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hI)
    have h3 : K * (∫ x in cube d, pk x ^ n) * (∫ x in cube d, pk x ^ n)⁻¹ ≤ K := by
      rw [mul_assoc]
      exact mul_le_of_le_one_right hK0 mul_inv_le_one
    rw [smul_eq_mul]
    calc _ = _ := by ring
      _ ≤ _ := h2
      _ ≤ K := h3
  have hlim := le_of_tendsto' (hT.const_mul (∑ m ∈ S, (N (fun j => z₀ j + (m j : ℝ)) - η))) hle
  rw [mul_one, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hlim
  have hfin : (S.card : ℝ) * η ≤ ε := by
    rw [hη, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  linarith
end Formalism.FourierDecayAlt.P
