-- Prove2me | solution 1 for GaussianPerimeter.VolumeComparison.weighted_amgm
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T11:15:36.900443+00:00
-- url     : https://prove2.me/submissions/56953486-1f42-4e86-92a9-097d14dc2bd6

import Mathlib

open Real

theorem solution {θ a b : ℝ} (hθ : 0 < θ ∧ θ < 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ((1-θ)^(1-θ) * θ^θ)⁻¹ * a^(1-θ) * b^θ ≤ a + b := by
  have h1 : 0 < 1 - θ := by linarith [hθ.2]
  have h2 : 0 < θ := hθ.1
  have hamgm := geom_mean_le_arith_mean2_weighted (le_of_lt h1) (le_of_lt h2)
    (div_nonneg ha (le_of_lt h1)) (div_nonneg hb (le_of_lt h2)) (by ring : (1-θ) + θ = 1)
  have hdiv1 : (a / (1-θ)) ^ (1-θ) = a^(1-θ) / (1-θ)^(1-θ) :=
    div_rpow ha (le_of_lt h1) (1-θ)
  have hdiv2 : (b / θ) ^ θ = b^θ / θ^θ := div_rpow hb (le_of_lt h2) θ
  have hrhs : (1-θ) * (a/(1-θ)) + θ * (b/θ) = a + b := by
    field_simp [ne_of_gt h1, ne_of_gt h2]
  rw [hdiv1, hdiv2, hrhs] at hamgm
  have hL : a^(1-θ) / (1-θ)^(1-θ) * (b^θ / θ^θ) =
      ((1-θ)^(1-θ) * θ^θ)⁻¹ * a^(1-θ) * b^θ := by
    field_simp [ne_of_gt (rpow_pos_of_pos h1 (1-θ)), ne_of_gt (rpow_pos_of_pos h2 θ)]
  rw [← hL]
  exact hamgm
