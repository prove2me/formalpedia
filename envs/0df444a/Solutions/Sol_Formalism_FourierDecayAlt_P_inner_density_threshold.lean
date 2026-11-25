-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.inner_density_threshold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:41:45.250716+00:00
-- url     : https://prove2.me/submissions/387b5e95-2f12-4552-a4b3-37f9f29d8357

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
theorem _root_.solution : C6.DensThreshJ := by
  intro C₁ c₃ C₂ hC₁ hc₃
  set K : ℝ := 24 * C₁ + 192 * c₃ + 5 * (C₂ : ℝ) + 80 with hK
  refine ⟨⌈K⌉₊, ?_⟩
  intro CV hCV r n s A hr hn hs hA
  have hKV : K ≤ (CV : ℝ) := le_trans (Nat.le_ceil K) (by exact_mod_cast hCV)
  have hx : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hxy : 2 * (r:ℝ) + 2 ≤ n := by exact_mod_cast hn
  have hsx : (s:ℝ) ≤ r := by exact_mod_cast hs
  have hy : (1:ℝ) ≤ n := by linarith
  have hK0 : 0 ≤ K := by positivity
  have hA' : K * ((r:ℝ) ^ 4 * n + (r:ℝ) ^ 5) ≤ A := by
    unfold C6.AV at hA
    have e : (r:ℝ) * ((CV:ℝ) * ((r:ℝ) ^ 3 * n + (n:ℝ) ^ 2 + (r:ℝ) ^ 4)) =
        (CV:ℝ) * ((r:ℝ) ^ 4 * n + (r:ℝ) ^ 5) + (CV:ℝ) * ((r:ℝ) * n ^ 2) := by ring
    rw [e] at hA
    have : 0 ≤ (CV:ℝ) * ((r:ℝ) * n ^ 2) := by positivity
    have : K * ((r:ℝ) ^ 4 * n + (r:ℝ) ^ 5) ≤ (CV:ℝ) * ((r:ℝ) ^ 4 * n + (r:ℝ) ^ 5) :=
      mul_le_mul_of_nonneg_right hKV (by positivity)
    linarith
  have hs2 : (s:ℝ) ^ 2 ≤ (r:ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hsx 2
  have h8 : 8 * (2 * (r:ℝ) + 1) ≤ 24 * r := by linarith
  have x35 : (r:ℝ) ^ 3 ≤ (r:ℝ) ^ 5 := pow_le_pow_right₀ hx (by norm_num)
  have x15 : (r:ℝ) ≤ (r:ℝ) ^ 5 := by
    calc (r:ℝ) = (r:ℝ) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hx (by norm_num)
  have x24 : (r:ℝ) ^ 2 * n ≤ (r:ℝ) ^ 4 * n :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hx (by norm_num)) (by positivity)
  have hpos : (0:ℝ) < 8 * (2 * (r:ℝ) + 1) := by positivity

  have hb : 5 * (r:ℝ) * (((C₂ * s ^ 2 : ℕ) : ℝ) + 1) + 2 * (r:ℝ) * ((1 : ℕ) : ℝ) ≤
      (5 * (C₂:ℝ) + 7) * (r:ℝ) ^ 5 := by
    push_cast
    have : (C₂:ℝ) * (s:ℝ) ^ 2 ≤ (C₂:ℝ) * (r:ℝ) ^ 2 := mul_le_mul_of_nonneg_left hs2 (by positivity)
    have e : 5 * (r:ℝ) * ((C₂:ℝ) * (r:ℝ) ^ 2 + 1) + 2 * (r:ℝ) = 5 * (C₂:ℝ) * (r:ℝ) ^ 3 + 7 * r := by ring
    have h3 : 5 * (r:ℝ) * ((C₂:ℝ) * (s:ℝ) ^ 2 + 1) ≤ 5 * (r:ℝ) * ((C₂:ℝ) * (r:ℝ) ^ 2 + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have := mul_le_mul_of_nonneg_left x35 (by positivity : (0:ℝ) ≤ 5 * (C₂:ℝ))
    nlinarith
  have key : ∀ X : ℝ, X * (8 * (2 * (r:ℝ) + 1)) + (5 * C₂ + 7) * (r:ℝ) ^ 5 ≤ A → X ≤ U.a1 r A (C₂ * s ^ 2) 1 := by
    intro X hX
    unfold U.a1
    rw [le_div_iff₀ hpos]
    linarith
  have hx5 : 0 ≤ (r:ℝ) ^ 5 := by positivity
  have hx4y : 0 ≤ (r:ℝ) ^ 4 * n := by positivity
  refine ⟨key _ ?_, key _ ?_, key _ ?_⟩
  · have a : C₁ * (s:ℝ) ^ 2 * (8 * (2 * (r:ℝ) + 1)) ≤ C₁ * (r:ℝ) ^ 2 * (24 * r) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hs2 hC₁) h8 (by positivity) (by positivity)
    have e : C₁ * (r:ℝ) ^ 2 * (24 * r) = 24 * C₁ * (r:ℝ) ^ 3 := by ring
    have := mul_le_mul_of_nonneg_left x35 (by positivity : (0:ℝ) ≤ 24 * C₁)
    have : K * ((r:ℝ) ^ 4 * n + (r:ℝ) ^ 5) = K * ((r:ℝ) ^ 4 * n) + K * (r:ℝ) ^ 5 := by ring
    have : 0 ≤ K * ((r:ℝ) ^ 4 * n) := by positivity
    have : 0 ≤ 192 * c₃ * (r:ℝ) ^ 5 := by positivity
    have : K * (r:ℝ) ^ 5 = (24 * C₁ + 5 * C₂ + 7) * (r:ℝ) ^ 5 + 192 * c₃ * (r:ℝ) ^ 5 + 73 * (r:ℝ) ^ 5 := by
      rw [hK]; ring
    nlinarith
  · have q1 : ((r:ℝ) + 1) ^ 2 ≤ 4 * (r:ℝ) ^ 2 := by nlinarith
    have q2 : (r:ℝ) * n + 1 ≤ 2 * ((r:ℝ) * n) := by nlinarith
    have q : ((r:ℝ) + 1) ^ 2 * ((r:ℝ) * n + 1) * (8 * (2 * (r:ℝ) + 1)) ≤
        4 * (r:ℝ) ^ 2 * (2 * ((r:ℝ) * n)) * (24 * r) :=
      mul_le_mul (mul_le_mul q1 q2 (by positivity) (by positivity)) h8 (by positivity) (by positivity)
    have e : 4 * (r:ℝ) ^ 2 * (2 * ((r:ℝ) * n)) * (24 * r) = 192 * ((r:ℝ) ^ 4 * n) := by ring
    have := mul_le_mul_of_nonneg_left q hc₃
    have : c₃ * ((r:ℝ) + 1) ^ 2 * ((r:ℝ) * n + 1) * (8 * (2 * (r:ℝ) + 1)) =
        c₃ * (((r:ℝ) + 1) ^ 2 * ((r:ℝ) * n + 1) * (8 * (2 * (r:ℝ) + 1))) := by ring
    have : K * ((r:ℝ) ^ 4 * n + (r:ℝ) ^ 5) = (192 * c₃) * ((r:ℝ) ^ 4 * n) + (5 * C₂ + 7) * (r:ℝ) ^ 5 +
        ((24 * C₁ + 5 * C₂ + 80) * ((r:ℝ) ^ 4 * n) + (24 * C₁ + 192 * c₃ + 73) * (r:ℝ) ^ 5) := by rw [hK]; ring
    have : 0 ≤ (24 * C₁ + 5 * C₂ + 80) * ((r:ℝ) ^ 4 * n) + (24 * C₁ + 192 * c₃ + 73) * (r:ℝ) ^ 5 := by positivity
    nlinarith
  · have q : (2 * (r:ℝ) * n + 1) * (8 * (2 * (r:ℝ) + 1)) ≤ (3 * ((r:ℝ) * n)) * (24 * r) :=
      mul_le_mul (by nlinarith) h8 (by positivity) (by positivity)
    have e : (3 * ((r:ℝ) * n)) * (24 * r) = 72 * ((r:ℝ) ^ 2 * n) := by ring
    have : K * ((r:ℝ) ^ 4 * n + (r:ℝ) ^ 5) = 72 * ((r:ℝ) ^ 4 * n) + (5 * C₂ + 7) * (r:ℝ) ^ 5 +
        ((24 * C₁ + 192 * c₃ + 5 * C₂ + 8) * ((r:ℝ) ^ 4 * n) + (24 * C₁ + 192 * c₃ + 73) * (r:ℝ) ^ 5) := by rw [hK]; ring
    have : 0 ≤ (24 * C₁ + 192 * c₃ + 5 * C₂ + 8) * ((r:ℝ) ^ 4 * n) + (24 * C₁ + 192 * c₃ + 73) * (r:ℝ) ^ 5 := by positivity
    nlinarith
end Formalism.FourierDecayAlt.P
