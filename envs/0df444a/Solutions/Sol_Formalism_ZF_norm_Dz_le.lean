-- Prove2me | solution 1 for Formalism.ZF.norm_Dz_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:38:10.99825+00:00
-- url     : https://prove2.me/submissions/a440b910-d07b-42e4-b33f-975421a750e0

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RiemannZetaOneEqOneSubOfRePos
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZetaGrowth
import Theorems.Thm_Formalism_ZF_ComplexPowerDifferenceIntegral_norm_dz_le
import Theorems.Thm_Formalism_ZF_ComplexPowerDifferenceIntegral_summable_norm_dz


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.ZF
open ComplexPowerDifferenceIntegral
namespace Formalism.ZF
theorem _root_.solution {s : ℂ} (hs : 0 < s.re) :
    ‖Dz s‖ ≤ ‖s - 1‖ * ‖s‖ * (1 + 1 / s.re) := by
  set σ := s.re with hσ

  have hkey : ∀ x : ℝ, 1 ≤ x → σ * (x + 1) ^ (-σ - 1) ≤ x ^ (-σ) - (x + 1) ^ (-σ) := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have hy0 : 0 < x + 1 := by linarith
    have hA : 0 < (x + 1) ^ σ := Real.rpow_pos_of_pos hy0 σ
    have hB : 0 < x ^ σ := Real.rpow_pos_of_pos hx0 σ
    have hq : 0 < (x + 1) / x := div_pos hy0 hx0
    have hr : ((x + 1) / x) ^ σ = (x + 1) ^ σ / x ^ σ := Real.div_rpow hy0.le hx0.le σ
    have hlog : 1 / (x + 1) ≤ Real.log ((x + 1) / x) := by
      have := Real.one_sub_inv_le_log_of_pos hq
      have e : 1 - ((x + 1) / x)⁻¹ = 1 / (x + 1) := by field_simp; ring
      linarith
    have hexp : 1 + σ / (x + 1) ≤ (x + 1) ^ σ / x ^ σ := by
      rw [← hr, Real.rpow_def_of_pos hq]
      have h1 := Real.add_one_le_exp (Real.log ((x + 1) / x) * σ)
      have h2 : σ / (x + 1) ≤ Real.log ((x + 1) / x) * σ := by
        rw [div_eq_mul_one_div, mul_comm]
        exact mul_le_mul_of_nonneg_right hlog hs.le
      linarith
    rw [Real.rpow_sub_one hy0.ne', Real.rpow_neg hy0.le, Real.rpow_neg hx0.le]
    have e1 : σ * ((x + 1) ^ σ)⁻¹ / (x + 1) = σ / (x + 1) * ((x + 1) ^ σ)⁻¹ := by ring
    have e2 : (x ^ σ)⁻¹ - ((x + 1) ^ σ)⁻¹ = ((x + 1) ^ σ / x ^ σ - 1) * ((x + 1) ^ σ)⁻¹ := by
      field_simp
    rw [mul_div_assoc', e1, e2]
    exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 hA.le)
  have hS : ∀ N : ℕ, ∑ i ∈ Finset.range (N + 1), ((i : ℝ) + 1) ^ (-σ - 1)
      ≤ 1 + (1 - ((N : ℝ) + 1) ^ (-σ)) / σ := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have hk := hkey ((N : ℝ) + 1) (by linarith [N.cast_nonneg (α := ℝ)])
      have hk' : ((N : ℝ) + 1 + 1) ^ (-σ - 1) ≤ (((N : ℝ) + 1) ^ (-σ) - ((N : ℝ) + 1 + 1) ^ (-σ)) / σ := by
        rw [le_div_iff₀ hs]
        linarith
      push_cast
      have e : (1 - ((N : ℝ) + 1) ^ (-σ)) / σ + (((N : ℝ) + 1) ^ (-σ) - ((N : ℝ) + 1 + 1) ^ (-σ)) / σ
          = (1 - ((N : ℝ) + 1 + 1) ^ (-σ)) / σ := by
        field_simp
        ring
      linarith
  have hT : ∀ n : ℕ, ∑ i ∈ Finset.range n, ((i : ℝ) + 1) ^ (-σ - 1) ≤ 1 + 1 / σ := by
    intro n
    rcases n with _ | N
    · simp only [Finset.range_zero, Finset.sum_empty]
      positivity
    · refine (hS N).trans ?_
      have h0 : 0 ≤ ((N : ℝ) + 1) ^ (-σ) := Real.rpow_nonneg (by positivity) _
      have : (1 - ((N : ℝ) + 1) ^ (-σ)) / σ ≤ 1 / σ := div_le_div_of_nonneg_right (by linarith) hs.le
      linarith
  have hC : 0 ≤ ‖s - 1‖ * ‖s‖ := by positivity
  show ‖∑' n, dz s n‖ ≤ _
  calc ‖∑' n, dz s n‖ ≤ ∑' n, ‖dz s n‖ := norm_tsum_le_tsum_norm (summable_norm_dz hs)
    _ ≤ ‖s - 1‖ * ‖s‖ * (1 + 1 / σ) := by
      refine Real.tsum_le_of_sum_range_le (fun n => norm_nonneg _) fun n => ?_
      calc ∑ i ∈ Finset.range n, ‖dz s i‖
          ≤ ∑ i ∈ Finset.range n, ‖s - 1‖ * ‖s‖ * ((i : ℝ) + 1) ^ (-σ - 1) :=
            Finset.sum_le_sum fun i _ => norm_dz_le hs i
        _ = ‖s - 1‖ * ‖s‖ * ∑ i ∈ Finset.range n, ((i : ℝ) + 1) ^ (-σ - 1) := by
            rw [Finset.mul_sum]
        _ ≤ ‖s - 1‖ * ‖s‖ * (1 + 1 / σ) := mul_le_mul_of_nonneg_left (hT n) hC
end Formalism.ZF
