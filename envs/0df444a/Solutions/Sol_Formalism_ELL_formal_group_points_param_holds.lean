-- Prove2me | solution 1 for Formalism.ELL.formal_group_points_param_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:53.040155+00:00
-- url     : https://prove2.me/submissions/0fb181c7-c55a-4f8f-b39d-48b518ab08f9

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsParamDef
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_nle
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_neq
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_sm
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_smm
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_smp
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_norm_one_sub
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_norm_two_le
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_norm_three_le
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_eval_w

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open FormalGroupPointsParam
namespace Formalism.ELL
theorem _root_.solution : FormalGroupPointsParametrisation.{u} := by
  intro K _ _ _ W w hW hw
  refine ⟨fun t ht0 ht1 => ?_, fun x y hxy hx => ?_⟩
  · obtain ⟨weq, hn⟩ := eval_w hW hw ht1
    set ω := evalPS w t with hω
    have hω0 : ω ≠ 0 := by
      rw [← norm_pos_iff, hn]; positivity
    have hω1 : ‖ω‖ < 1 := by
      rw [hn]; exact pow_lt_one₀ (norm_nonneg _) ht1 (by norm_num)
    refine ⟨hω0, ?_, ?_, ?_⟩
    · rw [WeierstrassCurve.Affine.nonsingular_iff']
      have heq : (-1 / ω) ^ 2 + W.a₁ * (t / ω) * (-1 / ω) + W.a₃ * (-1 / ω)
          - ((t / ω) ^ 3 + W.a₂ * (t / ω) ^ 2 + W.a₄ * (t / ω) + W.a₆) = 0 := by
        have k : ((-1 / ω) ^ 2 + W.a₁ * (t / ω) * (-1 / ω) + W.a₃ * (-1 / ω)
            - ((t / ω) ^ 3 + W.a₂ * (t / ω) ^ 2 + W.a₄ * (t / ω) + W.a₆)) * ω ^ 3
            = ω - (t ^ 3 + W.a₁ * t * ω + W.a₂ * t ^ 2 * ω + W.a₃ * ω ^ 2 + W.a₄ * t * ω ^ 2
              + W.a₆ * ω ^ 3) := by
          field_simp; ring
        rw [sub_eq_zero.mpr weq] at k
        exact (mul_eq_zero.mp k).resolve_right (pow_ne_zero _ hω0)
      refine ⟨(WeierstrassCurve.Affine.equation_iff' _ _).mpr heq, ?_⟩
      by_contra hc
      push Not at hc
      obtain ⟨hA, hB⟩ := hc
      have eA : -W.a₁ * ω - 3 * t ^ 2 - 2 * W.a₂ * t * ω - W.a₄ * ω ^ 2 = 0 := by
        have k : -W.a₁ * ω - 3 * t ^ 2 - 2 * W.a₂ * t * ω - W.a₄ * ω ^ 2
            = ω ^ 2 * (W.a₁ * (-1 / ω) - (3 * (t / ω) ^ 2 + 2 * W.a₂ * (t / ω) + W.a₄)) := by
          field_simp; ring
        rw [k, hA, mul_zero]
      have eB : -2 + W.a₁ * t + W.a₃ * ω = 0 := by
        have k : -2 + W.a₁ * t + W.a₃ * ω = ω * (2 * (-1 / ω) + W.a₁ * (t / ω) + W.a₃) := by
          field_simp
          try ring
        rw [k, hB, mul_zero]
      set Q := W.a₁ * t + W.a₂ * t ^ 2 + (2 * W.a₃) * ω + (2 * W.a₄) * (t * ω)
        + (3 * W.a₆) * ω ^ 2 with hQ
      have kQ : ω * (1 - Q) = 0 := by
        rw [hQ]; linear_combination ω * eB - t * eA + 3 * weq
      have ht2 : ‖t ^ 2‖ < 1 := by rw [sq]; exact FormalGroupPointsParam.smp ht1 ht1
      have two : ∀ a : K, ‖a‖ ≤ 1 → ‖2 * a‖ ≤ 1 := fun a ha => by
        rw [norm_mul]; exact mul_le_one₀ norm_two_le (norm_nonneg _) ha
      have three : ∀ a : K, ‖a‖ ≤ 1 → ‖3 * a‖ ≤ 1 := fun a ha => by
        rw [norm_mul]; exact mul_le_one₀ norm_three_le (norm_nonneg _) ha
      have hQ1 : ‖Q‖ < 1 :=
        sm (sm (sm (sm (smm hW.1 ht1) (smm hW.2.1 ht2)) (smm (two _ hW.2.2.1) hω1))
          (smm (two _ hW.2.2.2.1) (smp ht1 hω1)))
          (smm (three _ hW.2.2.2.2) (by rw [sq]; exact smp hω1 hω1))
      have h1Q : (1 - Q) ≠ 0 := fun h => by
        have := norm_one_sub hQ1; rw [h, norm_zero] at this; exact zero_ne_one this
      exact (mul_ne_zero hω0 h1Q) kQ
    · rw [norm_div, hn, lt_div_iff₀ (by positivity), one_mul]
      have h2 : ‖t‖ ^ 2 < 1 := pow_lt_one₀ (norm_nonneg _) ht1 (by norm_num)
      calc ‖t‖ ^ 3 = ‖t‖ * ‖t‖ ^ 2 := by ring
        _ < ‖t‖ * 1 := mul_lt_mul_of_pos_left h2 ht0
        _ = ‖t‖ := mul_one _
    · field_simp
  ·
    have hx0 : x ≠ 0 := by
      rw [← norm_pos_iff]; linarith
    have heq : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
      (WeierstrassCurve.Affine.equation_iff _ _).mp hxy.1
    have hx1 : (1 : ℝ) ≤ ‖x‖ := hx.le
    have hxx : ‖x‖ ≤ ‖x‖ ^ 2 := by nlinarith
    have hx23 : ‖x‖ ^ 2 < ‖x‖ ^ 3 := by
      have : 0 < ‖x‖ ^ 2 := by positivity
      nlinarith
    have hlow : ‖W.a₂ * x ^ 2 + W.a₄ * x + W.a₆‖ ≤ ‖x‖ ^ 2 := by
      refine nle (nle ?_ ?_) ?_
      · rw [norm_mul, norm_pow]; exact mul_le_of_le_one_left (by positivity) hW.2.1
      · rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) hW.2.2.2.1).trans hxx
      · exact hW.2.2.2.2.trans (by nlinarith)
    have hRn : ‖x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆‖ = ‖x‖ ^ 3 := by
      have : x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ = x ^ 3 + (W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) := by
        ring
      rw [this, neq (by rw [norm_pow]; exact lt_of_le_of_lt hlow hx23), norm_pow]
    have hLf : y ^ 2 + W.a₁ * x * y + W.a₃ * y = y * (y + (W.a₁ * x + W.a₃)) := by ring
    rw [← heq, hLf, norm_mul] at hRn

    have hmid : ‖W.a₁ * x + W.a₃‖ ≤ ‖x‖ := by
      refine nle ?_ (hW.2.2.1.trans hx1)
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) hW.1
    have hyx : ‖x‖ < ‖y‖ := by
      by_contra hc
      push Not at hc
      have h1 : ‖y + (W.a₁ * x + W.a₃)‖ ≤ ‖x‖ := nle hc hmid
      have : ‖y‖ * ‖y + (W.a₁ * x + W.a₃)‖ ≤ ‖x‖ * ‖x‖ :=
        mul_le_mul hc h1 (norm_nonneg _) (norm_nonneg _)
      nlinarith
    have hY : ‖y‖ ^ 2 = ‖x‖ ^ 3 := by
      rw [← hRn, neq (lt_of_le_of_lt hmid hyx), sq]
    have hy0 : y ≠ 0 := by
      rw [← norm_pos_iff]; linarith
    have hxpos : 0 < ‖x‖ := by linarith
    have hypos : 0 < ‖y‖ := by linarith
    set z := -x / y with hz
    have hzn : ‖z‖ = ‖x‖ / ‖y‖ := by rw [hz, norm_div, norm_neg]
    have hz0 : 0 < ‖z‖ := by rw [hzn]; positivity
    have hz1 : ‖z‖ < 1 := by rw [hzn, div_lt_one hypos]; exact hyx
    refine ⟨hz0, hz1, ?_⟩
    obtain ⟨weq', hn'⟩ := eval_w hW hw hz1
    set ω' := evalPS w z with hω'
    set ω := -1 / y with hω
    have hωn : ‖ω‖ = ‖z‖ ^ 3 := by
      rw [hω, hzn, norm_div, norm_neg, norm_one, div_pow, ← hY]
      field_simp
    have weq : ω = z ^ 3 + W.a₁ * z * ω + W.a₂ * z ^ 2 * ω + W.a₃ * ω ^ 2 + W.a₄ * z * ω ^ 2
        + W.a₆ * ω ^ 3 := by
      rw [hω, hz]
      field_simp
      linear_combination -heq
    have hω1 : ‖ω‖ < 1 := by rw [hωn]; exact pow_lt_one₀ (norm_nonneg _) hz1 (by norm_num)
    have hω'1 : ‖ω'‖ < 1 := by rw [hn']; exact pow_lt_one₀ (norm_nonneg _) hz1 (by norm_num)
    set E := W.a₁ * z + W.a₂ * z ^ 2 + W.a₃ * (ω + ω') + W.a₄ * (z * (ω + ω'))
      + W.a₆ * (ω ^ 2 + ω * ω' + ω' ^ 2) with hE
    have hz2 : ‖z ^ 2‖ < 1 := by rw [sq]; exact smp hz1 hz1
    have hs : ‖ω + ω'‖ < 1 := sm hω1 hω'1
    have hE1 : ‖E‖ < 1 :=
      sm (sm (sm (sm (smm hW.1 hz1) (smm hW.2.1 hz2)) (smm hW.2.2.1 hs))
        (smm hW.2.2.2.1 (smp hz1 hs)))
        (smm hW.2.2.2.2 (sm (sm (by rw [sq]; exact smp hω1 hω1) (smp hω1 hω'1))
          (by rw [sq]; exact smp hω'1 hω'1)))
    have key : (ω - ω') * (1 - E) = 0 := by
      rw [hE]; linear_combination weq - weq'
    have h1E : (1 - E) ≠ 0 := fun h => by
      have := norm_one_sub hE1; rw [h, norm_zero] at this; exact zero_ne_one this
    have hωω : ω = ω' := sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right h1E)
    rw [← hωω, hω, hz]
    constructor
    · field_simp
    · field_simp
end Formalism.ELL
