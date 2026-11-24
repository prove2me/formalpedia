-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.four_term_sum_bound_of_parameters
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:51:11.021875+00:00
-- url     : https://prove2.me/submissions/52f04c01-6cf5-4701-8d6f-dba051ac7835

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_FourTermSumBoundOfParameters
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_FourTermSumBoundOfParameters
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_four_term_sum_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LatticeBaseChangeAlt
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution : FourTermSumBoundOfParameters := by
  intro d PP D κ T c RR ga C k f b m δ₂ q DF g₀ hd hT hTga hPP hD hRR hq hC hk hf hb hm hδ
    hκ h0 hTlow hc hg₀ hTc hqlow hTPP hPP2
  have hga : 0 < ga := lt_of_lt_of_le hT hTga
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hK : 0 ≤ C * k * f * b := by positivity
  have hD0 : 0 ≤ D := by linarith
  have hPP1 : 1 ≤ PP := by nlinarith
  have hT1 : 1 ≤ T := by linarith
  have hRRc : RR ^ 2 * c ≤ 1 / PP ^ 2 := by
    have hP2 : 0 < PP ^ 2 := by positivity
    rw [hc, le_div_iff₀ hP2]
    have e : RR ^ 2 * (RR * PP * DF ^ 2 / q) * PP ^ 2 = RR ^ 3 * PP ^ 3 * DF ^ 2 / q := by ring
    rw [e, div_le_one hq]
    have h34 : RR ^ 3 ≤ RR ^ 4 := pow_le_pow_right₀ hRR (by norm_num)
    have : RR ^ 3 * (PP ^ 3 * DF ^ 2) ≤ RR ^ 4 * (PP ^ 3 * DF ^ 2) :=
      mul_le_mul_of_nonneg_right h34 (by positivity)
    nlinarith [this]
  have hmδ : 0 < m * δ₂ := mul_pos hm hδ
  have h1 : PP ^ 2 * D ^ 3 * C * k * f * b / T ≤ f * m * b * δ₂ / 4 := by
    rw [div_le_iff₀ hmδ] at hTlow
    rw [div_le_iff₀ hT]
    have := mul_le_mul_of_nonneg_right hTlow (mul_nonneg hf hb)
    nlinarith [this]
  have hPPq : PP ^ 2 ≤ f * m * b * δ₂ / 4 := by
    have a : PP ^ 2 * 1 ≤ PP ^ 2 * (PP * T) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    nlinarith [a]
  have h2 : PP ^ 2 * T * c ≤ f * m * b * δ₂ / 4 := by
    have hTc0 : 0 ≤ T * c := mul_nonneg hT.le hc0
    have hTc1 : T * c ≤ 1 := by nlinarith
    have : PP ^ 2 * (T * c) ≤ PP ^ 2 * 1 := mul_le_mul_of_nonneg_left hTc1 (by positivity)
    nlinarith [this]
  have hside : 1 + PP ^ 2 / T ≤ PP ^ 2 * D ^ 3 := by
    have s1 : PP ^ 2 / T ≤ 1 := (div_le_one hT).2 hTPP
    have s2 : (1 : ℝ) ≤ D ^ 3 := one_le_pow₀ hD
    have s3 : PP ^ 2 * 1 ≤ PP ^ 2 * D ^ 3 := mul_le_mul_of_nonneg_left s2 (by positivity)
    linarith
  have h3 : PP ^ 2 * (RR ^ 2 * c + 1 / T) * C * k * f * b / ga ≤ f * m * b * δ₂ / 4 := by
    have a1 : PP ^ 2 * (RR ^ 2 * c + 1 / T) ≤ PP ^ 2 * D ^ 3 := by
      have : PP ^ 2 * (RR ^ 2 * c) ≤ PP ^ 2 * (1 / PP ^ 2) :=
        mul_le_mul_of_nonneg_left hRRc (by positivity)
      have e : PP ^ 2 * (1 / PP ^ 2) = 1 := by field_simp
      have e' : PP ^ 2 * (1 / T) = PP ^ 2 / T := by ring
      rw [mul_add, e']
      linarith
    have a2 : PP ^ 2 * (RR ^ 2 * c + 1 / T) * (C * k * f * b) ≤ PP ^ 2 * D ^ 3 * (C * k * f * b) :=
      mul_le_mul_of_nonneg_right a1 hK
    calc PP ^ 2 * (RR ^ 2 * c + 1 / T) * C * k * f * b / ga
        = PP ^ 2 * (RR ^ 2 * c + 1 / T) * (C * k * f * b) / ga := by ring
      _ ≤ PP ^ 2 * D ^ 3 * (C * k * f * b) / ga := by gcongr
      _ ≤ PP ^ 2 * D ^ 3 * (C * k * f * b) / T := by gcongr
      _ = PP ^ 2 * D ^ 3 * C * k * f * b / T := by ring
      _ ≤ _ := h1
  exact four_term_sum_bound d PP D κ T c RR ga C k f b m δ₂ hd hT hga hPP.le hD0 (by positivity) hκ
    h0 h1 h2 h3
end Formalism.LatticeBaseChangeAlt
