-- Prove2me | solution 1 for CosDensity.distinguish
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:05:54.45689+00:00
-- url     : https://prove2.me/submissions/0527c3d0-edad-47a0-97f9-52d56a05b4e1

import Mathlib
import Definitions.Def_CosDensity_Stream

open CosDensity in
theorem solution (X₀ X₁ φ ε : ℝ) (hX₀ : 0 < X₀) (hφ : 1 < φ) (hX : φ * X₀ ≤ X₁)
    (hε0 : 0 < ε) (hε : ε < (φ - 1) / (φ + 1)) :
    (1 + ε) * X₀ < (1 - ε) * X₁ ∧
      ∀ M₀ M₁ Y₀ Y₁ : ℝ, 0 ≤ M₀ → M₀ ≤ X₀ → X₁ ≤ M₁ →
        IsApprox ε M₀ Y₀ → IsApprox ε M₁ Y₁ → Y₀ < Y₁ := by
  have hφ1 : 0 < φ + 1 := by linarith
  have h1 : ε * (φ + 1) < φ - 1 := (lt_div_iff₀ hφ1).mp hε
  have hεlt : ε < 1 := by nlinarith
  have hkey : 1 + ε < φ * (1 - ε) := by nlinarith
  have hA : (1 + ε) * X₀ < (1 - ε) * X₁ := by
    have h2 : (1 + ε) * X₀ < φ * (1 - ε) * X₀ := mul_lt_mul_of_pos_right hkey hX₀
    have h3 : (1 - ε) * (φ * X₀) ≤ (1 - ε) * X₁ :=
      mul_le_mul_of_nonneg_left hX (by linarith)
    nlinarith
  refine ⟨hA, ?_⟩
  intro M₀ M₁ Y₀ Y₁ hM0 hM0X hM1 hY0 hY1
  obtain ⟨_, hY0u⟩ := hY0
  obtain ⟨hY1l, _⟩ := hY1
  have h4 : (1 + ε) * M₀ ≤ (1 + ε) * X₀ := mul_le_mul_of_nonneg_left hM0X (by linarith)
  have h5 : (1 - ε) * X₁ ≤ (1 - ε) * M₁ := mul_le_mul_of_nonneg_left hM1 (by linarith)
  linarith
