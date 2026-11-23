-- Prove2me | solution 1 for Formalism.ExtensionFiltration.weight_shift_constant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:30:36.098489+00:00
-- url     : https://prove2.me/submissions/f67642f2-bd67-4394-9da0-58114795d878

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_CovolumeEstimateAnchoredWeights
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeAssemblyHolds
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeFullAssemblyHolds
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeIntoDivisionHolds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_SpanMuMin
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_TwistLower
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_MuMaxMinkowski
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GlobalBoundRefinements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.ExtensionFiltration
open Finset Module NumberField
namespace Formalism.ExtensionFiltration
theorem _root_.solution : WShiftConst := by
  intro Pl _ w w0 lcvD pq logOm C3 B0 llx La f m k Δ b xe CO h1 hw hΔ hpq hCO hlog hLa hf hm hk hkΔ hB0 hllx
  subst hB0
  have hL0 : 0 ≤ CO * La := le_trans (abs_nonneg _) hlog
  have hLa0 : 0 ≤ La := by nlinarith
  have hpqa : |pq| ≤ k + m := by
    have h := abs_sub_abs_le_abs_sub pq k
    rw [abs_of_pos (by linarith : (0:ℝ) < k)] at h
    linarith
  have hkm : 0 ≤ k + m := by linarith
  have hX0 : 0 ≤ (k + m) * Δ := mul_nonneg hkm hΔ
  have hterm : ∀ ρ, pq * w ρ * logOm ≤ pq * w0 ρ * logOm + (k + m) * Δ * (CO * La) := by
    intro ρ
    have habs : |pq * (w ρ - w0 ρ) * logOm| ≤ (k + m) * Δ * (CO * La) := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul hpqa (hw ρ) (abs_nonneg _) hkm) hlog (abs_nonneg _) hX0
    have e : pq * w ρ * logOm = pq * w0 ρ * logOm + pq * (w ρ - w0 ρ) * logOm := by ring
    rw [e]
    linarith [le_abs_self (pq * (w ρ - w0 ρ) * logOm)]
  have hsum : ∑ ρ, pq * w ρ * logOm ≤
      ∑ ρ, pq * w0 ρ * logOm + (Fintype.card Pl : ℝ) * ((k + m) * Δ * (CO * La)) := by
    calc ∑ ρ, pq * w ρ * logOm ≤ ∑ ρ, (pq * w0 ρ * logOm + (k + m) * Δ * (CO * La)) :=
          Finset.sum_le_sum fun ρ _ => hterm ρ
      _ = ∑ ρ, pq * w0 ρ * logOm + (Fintype.card Pl : ℝ) * ((k + m) * Δ * (CO * La)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hf0 : 0 ≤ f := le_trans (Nat.cast_nonneg _) hf
  have hm0 : 0 ≤ m := by linarith
  have hb0 : 0 ≤ b := by linarith [mul_nonneg (by linarith : (0:ℝ) ≤ k) hΔ]
  have hxe0 : 0 ≤ xe := by linarith
  have hXY : (k + m) * Δ ≤ 4 * m * b := by
    linarith [mul_nonneg hm0 (by linarith : (0:ℝ) ≤ 2 * b - k * Δ),
      mul_nonneg (mul_nonneg hm0 hΔ) (by linarith : (0:ℝ) ≤ k - 1),
      mul_nonneg hb0 (by linarith : (0:ℝ) ≤ m - 1)]
  have hY0 : 0 ≤ 4 * m * b := mul_nonneg (mul_nonneg (by norm_num) hm0) hb0
  have hB0nn : 0 ≤ f * m * b * xe := mul_nonneg (mul_nonneg (mul_nonneg hf0 hm0) hb0) hxe0
  have hc1 : (Fintype.card Pl : ℝ) * ((k + m) * Δ * (CO * La)) ≤ f * ((k + m) * Δ * (CO * La)) :=
    mul_le_mul_of_nonneg_right hf (mul_nonneg hX0 hL0)
  have hc2 : f * ((k + m) * Δ * (CO * La)) ≤ f * (4 * m * b * (CO * (3 * xe))) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul hXY (mul_le_mul_of_nonneg_left hLa (by linarith)) hL0 hY0) hf0
  have hc3 : 0 ≤ CO * (f * m * b * xe) * (llx - 1) :=
    mul_nonneg (mul_nonneg (by linarith) hB0nn) (by linarith)
  linarith
end Formalism.ExtensionFiltration
