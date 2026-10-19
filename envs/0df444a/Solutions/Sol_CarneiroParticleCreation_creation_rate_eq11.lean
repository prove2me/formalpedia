-- Prove2me | solution 1 for CarneiroParticleCreation.creation_rate_eq11
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:35:19.90362+00:00
-- url     : https://prove2.me/submissions/203105dd-1097-4a30-854e-a0639b27e795

import Mathlib

theorem solution (Γ H ρm Λ : ℝ) (hH : H ≠ 0)
    (h8 : ρm + Λ = 3 * H ^ 2) (h10 : Λ = 2 * Γ * H) :
    Γ = 3 / 2 * (1 - ρm / (3 * H ^ 2)) * H := by
  have : ρm = 3 * H ^ 2 - 2 * Γ * H := by linarith
  rw [this]; field_simp; ring
