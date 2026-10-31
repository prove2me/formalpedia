-- Prove2me | solution 1 for BOGOPromo.NoStockpile.cBar_le_cTilde
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T19:50:20.799258+00:00
-- url     : https://prove2.me/submissions/56e9173b-32ba-4c29-83cd-5015aa7327df

import Mathlib
import Definitions.Def_BOGOPromo_NoStockpile_Model
open BOGOPromo.NoStockpile

theorem solution(θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) : cBar θ ≤ cTilde θ := by
  unfold cBar cTilde
  have h1 : (0:ℝ) < 1 + 2*θ := by linarith
  have h2 : (0:ℝ) < 1 + θ := by linarith
  have hb : Real.sqrt (2*θ/(1+2*θ)) ≤ 2 * Real.sqrt (θ/(1+θ)) := by
    rw [show (2:ℝ) * Real.sqrt (θ/(1+θ)) = Real.sqrt (4*(θ/(1+θ))) by
      rw [Real.sqrt_mul (by norm_num), show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ h1, show 4 * (θ / (1 + θ)) * (1 + 2 * θ) = (4*θ*(1+2*θ))/(1+θ) by ring, le_div_iff₀ h2]
    nlinarith
  have hx : θ * (4 * θ - 1) / (1 + 2 * θ) = θ - 2*θ*(1-θ)/(1+2*θ) := by field_simp; ring
  have hy : 0 ≤ 2*θ*(1-θ)/(1+2*θ) := by apply div_nonneg <;> nlinarith
  rw [hx]
  have h1θ : 0 ≤ 1 - θ := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hb h1θ, Real.sqrt_nonneg (2*θ/(1+2*θ))]
