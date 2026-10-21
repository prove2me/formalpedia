-- Prove2me | solution 1 for FastCLO.ETO.pointwise_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:05:57.178426+00:00
-- url     : https://prove2.me/submissions/88477bec-b557-4727-a61e-ca6752261821

import Mathlib
import Definitions.Def_FastCLO_ETO_Model

set_option autoImplicit false
open scoped InnerProductSpace

theorem solution {d : ℕ} (P : FastCLO.ETO.Polytope d) (u v z₁ z₂ : FastCLO.ERM.Vec d)
    (hz₁ : z₁ ∈ P.Z) (hz₂ : z₂ ∈ P.Z) (hopt : ∀ z ∈ P.Z, ⟪v, z₁⟫_ℝ ≤ ⟪v, z⟫_ℝ) :
    ⟪u, z₁ - z₂⟫_ℝ ≤ 2 * P.B * ‖u - v‖ := by
  have b1 : ‖z₁‖ ≤ P.B := P.bounded z₁ hz₁
  have b2 : ‖z₂‖ ≤ P.B := P.bounded z₂ hz₂
  have hnorm : ‖z₁ - z₂‖ ≤ 2 * P.B := by
    calc ‖z₁ - z₂‖ ≤ ‖z₁‖ + ‖z₂‖ := norm_sub_le _ _
      _ ≤ 2 * P.B := by linarith
  have h1 : ⟪u, z₁ - z₂⟫_ℝ = ⟪u - v, z₁ - z₂⟫_ℝ + ⟪v, z₁ - z₂⟫_ℝ := by
    rw [← inner_add_left]; congr 1; abel
  have h2 : ⟪v, z₁ - z₂⟫_ℝ ≤ 0 := by
    rw [inner_sub_right]; linarith [hopt z₂ hz₂]
  have h3 : ⟪u - v, z₁ - z₂⟫_ℝ ≤ ‖u - v‖ * ‖z₁ - z₂‖ := real_inner_le_norm _ _
  calc ⟪u, z₁ - z₂⟫_ℝ ≤ ‖u - v‖ * ‖z₁ - z₂‖ := by rw [h1]; linarith
    _ ≤ ‖u - v‖ * (2 * P.B) := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    _ = 2 * P.B * ‖u - v‖ := by ring
