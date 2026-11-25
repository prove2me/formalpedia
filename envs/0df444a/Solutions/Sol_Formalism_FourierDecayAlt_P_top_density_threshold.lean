-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.top_density_threshold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:51:59.584349+00:00
-- url     : https://prove2.me/submissions/758cb76f-5515-46a6-9118-8991cf714faa

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InnerDensityThreshold

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
set_option maxHeartbeats 2000000
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C6.DensThreshTop := by
  intro C₁ C C₂ hC₁ hC
  set K : ℝ := 40 * C₁ + 80 + 12 * C + 4 * C * C₂ + 2 * (C₂ : ℝ) + 1 with hK
  refine ⟨⌈K⌉₊, ?_⟩
  intro CV hCV r n s al A hr hn hs hal hA
  have hKV : K ≤ (CV : ℝ) := le_trans (Nat.le_ceil K) (by exact_mod_cast hCV)
  have hx : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hxy : 2 * (r:ℝ) + 2 ≤ n := by exact_mod_cast hn
  have hsx : (s:ℝ) ≤ r + 1 := by exact_mod_cast hs
  have hal' : (al:ℝ) ≤ C₂ * (s:ℝ) ^ 2 := by exact_mod_cast hal
  have hy : (1:ℝ) ≤ n := by linarith
  have hK0 : 0 ≤ K := by positivity
  constructor
  · have hA' : K * ((r:ℝ) * n ^ 2 + (r:ℝ) ^ 5) ≤ A := by
      unfold C6.AV at hA
      have e : (r:ℝ) * ((CV:ℝ) * ((r:ℝ) ^ 3 * n + (n:ℝ) ^ 2 + (r:ℝ) ^ 4)) =
          (CV:ℝ) * ((r:ℝ) * n ^ 2 + (r:ℝ) ^ 5) + (CV:ℝ) * ((r:ℝ) ^ 4 * n) := by ring
      rw [e] at hA
      have : 0 ≤ (CV:ℝ) * ((r:ℝ) ^ 4 * n) := by positivity
      have : K * ((r:ℝ) * n ^ 2 + (r:ℝ) ^ 5) ≤ (CV:ℝ) * ((r:ℝ) * n ^ 2 + (r:ℝ) ^ 5) :=
        mul_le_mul_of_nonneg_right hKV (by positivity)
      linarith
    have hs2 : (s:ℝ) ^ 2 ≤ 4 * (r:ℝ) ^ 2 := by
      have : (s:ℝ) ^ 2 ≤ ((r:ℝ) + 1) ^ 2 := pow_le_pow_left₀ (by positivity) hsx 2
      nlinarith
    have hR2 : ((r:ℝ) + 1) ^ 2 ≤ 4 * (r:ℝ) ^ 2 := by nlinarith
    have x35 : (r:ℝ) ^ 3 ≤ (r:ℝ) ^ 5 := pow_le_pow_right₀ hx (by norm_num)
    have hpos : (0:ℝ) < 5 * ((r:ℝ) + 1) := by positivity
    rw [le_sub_iff_add_le, le_div_iff₀ hpos, le_sub_iff_add_le]

    have b1 : (C₁ * (s:ℝ) ^ 2 + 2 * ((r:ℝ) + 1) ^ 2 + C * (r:ℝ) ^ 2) ≤ (4 * C₁ + 8 + C) * (r:ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hs2 hC₁
      nlinarith
    have b2 : (C₁ * (s:ℝ) ^ 2 + 2 * ((r:ℝ) + 1) ^ 2 + C * (r:ℝ) ^ 2) * (5 * ((r:ℝ) + 1)) ≤
        (4 * C₁ + 8 + C) * (r:ℝ) ^ 2 * (10 * r) :=
      mul_le_mul b1 (by linarith) (by positivity) (by positivity)
    have b3 : (r:ℝ) * al ≤ 4 * C₂ * (r:ℝ) ^ 3 := by
      have : (al:ℝ) ≤ C₂ * (4 * (r:ℝ) ^ 2) := le_trans hal' (mul_le_mul_of_nonneg_left hs2 (by positivity))
      have := mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ r)
      nlinarith
    have b4 : (n:ℝ) ^ 2 ≤ (r:ℝ) * n ^ 2 := by nlinarith [sq_nonneg (n:ℝ)]
    have b5 : C * ((n:ℝ) ^ 2 + (r:ℝ) ^ 3 + r * al) ≤ C * ((r:ℝ) * n ^ 2) + (C + 4 * C * C₂) * (r:ℝ) ^ 5 := by
      have : (n:ℝ) ^ 2 + (r:ℝ) ^ 3 + r * al ≤ (r:ℝ) * n ^ 2 + (1 + 4 * C₂) * (r:ℝ) ^ 5 := by nlinarith
      have := mul_le_mul_of_nonneg_left this hC
      nlinarith
    have e : (4 * C₁ + 8 + C) * (r:ℝ) ^ 2 * (10 * r) = (40 * C₁ + 80 + 10 * C) * (r:ℝ) ^ 3 := by ring
    have b6 := mul_le_mul_of_nonneg_left x35 (by positivity : (0:ℝ) ≤ 40 * C₁ + 80 + 10 * C)
    have : K * ((r:ℝ) * n ^ 2 + (r:ℝ) ^ 5) = C * ((r:ℝ) * n ^ 2) + (C + 4 * C * C₂) * (r:ℝ) ^ 5 +
        (40 * C₁ + 80 + 10 * C) * (r:ℝ) ^ 5 +
        ((40 * C₁ + 80 + 11 * C + 4 * C * C₂ + 2 * C₂ + 1) * ((r:ℝ) * n ^ 2) + (C + 2 * C₂ + 1) * (r:ℝ) ^ 5) := by
      rw [hK]; ring
    have : 0 ≤ (40 * C₁ + 80 + 11 * C + 4 * C * C₂ + 2 * C₂ + 1) * ((r:ℝ) * n ^ 2) + (C + 2 * C₂ + 1) * (r:ℝ) ^ 5 := by
      positivity
    nlinarith
  · have hK2 : (2 * C₂ + 1 : ℝ) ≤ K := by
      rw [hK]; have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hC) (Nat.cast_nonneg (α := ℝ) C₂); linarith
    have h2 : (2 * C₂ + 1 : ℝ) ≤ CV := le_trans hK2 hKV
    unfold C6.mmV
    have hR : ((C₂ * s ^ 2 + 1 : ℕ) : ℝ) ≤ ((CV * (r ^ 2 + 1) : ℕ) : ℝ) := by
      push_cast
      have q1 : (s:ℝ) ^ 2 ≤ ((r:ℝ) + 1) ^ 2 := pow_le_pow_left₀ (by positivity) hsx 2
      have q2 : ((r:ℝ) + 1) ^ 2 ≤ 2 * ((r:ℝ) ^ 2 + 1) := by nlinarith [sq_nonneg ((r:ℝ) - 1)]
      have q3 : (C₂:ℝ) * (s:ℝ) ^ 2 ≤ (C₂:ℝ) * (2 * ((r:ℝ) ^ 2 + 1)) :=
        mul_le_mul_of_nonneg_left (le_trans q1 q2) (by positivity)
      have q4 : (2 * (C₂:ℝ) + 1) * ((r:ℝ) ^ 2 + 1) ≤ (CV:ℝ) * ((r:ℝ) ^ 2 + 1) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
      have q5 : (1:ℝ) ≤ (r:ℝ) ^ 2 + 1 := by nlinarith
      nlinarith
    exact_mod_cast hR
end Formalism.FourierDecayAlt.P
