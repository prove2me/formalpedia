-- Prove2me | solution 1 for DerivativeChainPrivate.cubic_cube_boundary_gaps
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-19T11:15:55.961294+00:00
-- url     : https://prove2.me/submissions/3eaaf170-74ef-4a57-80d7-330bd3ed8588

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open Polynomial DerivativeChainPrivate
set_option autoImplicit false



set_option autoImplicit false
open scoped BigOperators

namespace DerivativeChainPrivate













end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate







end DerivativeChainPrivate

open DerivativeChainPrivate in
theorem solution :
    let r := Real.sqrt 2
    let α₀ := (5 - 3 * r) / 14
    let α₁ : ℝ := 1 / 28
    let b₀ := (32 - 15 * r) / 56
    let b₁ : ℝ := 1 / 7
    let M := 11 * r / 448
    0 < α₁ ∧ α₁ < α₀ ∧ 0 < M ∧
      b₁ - (α₁ / α₀) * b₀ = 3 * (2 - r) / 112 ∧
      0 < b₁ - (α₁ / α₀) * b₀ ∧
      b₀ - b₁ - 2 * M / (5 / 2) = (240 - 161 * r) / 560 ∧
      0 < b₀ - b₁ - 2 * M / (5 / 2) := by
  dsimp only
  have hr : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsmall : Real.sqrt 2 < 3 / 2 := by nlinarith only [hs, hr]
  have hα : 5 - 3 * Real.sqrt 2 ≠ 0 := ne_of_gt (by linarith)
  have heq : (1 / 7 : ℝ) - (1 / 28) / ((5 - 3 * Real.sqrt 2) / 14) *
      ((32 - 15 * Real.sqrt 2) / 56) = 3 * (2 - Real.sqrt 2) / 112 := by
    field_simp [hα]
    nlinarith only [hs]
  refine ⟨by norm_num, by linarith, by positivity, heq, ?_, ?_, ?_⟩
  · rw [heq]; linarith
  · ring
  · have hgap : 161 * Real.sqrt 2 < 240 := by nlinarith only [hs, hr]
    linarith
