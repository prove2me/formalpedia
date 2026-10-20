-- Prove2me | solution 1 for DerivativeChainPrivate.cubic_cube_negative_support_kernel
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-19T11:14:19.671873+00:00
-- url     : https://prove2.me/submissions/5659f4a7-3ba3-45cf-833f-793473a3c03f

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
theorem solution (X Y a : ℝ)
    (hX : 5 / 2 ≤ X) (hY : 0 ≤ Y) (ha : 0 ≤ a) (ha' : a ≤ 1 / 6) :
    0 < (X + a) ^ 2 + 2 * (X - a) * Y + Y ^ 2 ∧
      (2 * (X + Y) + a) / ((X + a) ^ 2 + 2 * (X - a) * Y + Y ^ 2) ≤ 4 / 5 := by
  have hx : 0 < X := by linarith
  have hxy : 0 ≤ 2 * (X - a) * Y := mul_nonneg (by linarith) hY
  have hD : 0 < (X + a) ^ 2 + 2 * (X - a) * Y + Y ^ 2 := by
    nlinarith only [sq_pos_of_pos (add_pos_of_pos_of_nonneg hx ha), hxy, sq_nonneg Y]
  refine ⟨hD, ?_⟩
  calc
    _ ≤ 2 / X := by
      apply (div_le_div_iff₀ hD hx).2
      have hterm : 0 ≤ (2 * X - 4 * a) * Y := mul_nonneg (by linarith) hY
      have hax : 0 ≤ a * X := mul_nonneg ha hx.le
      nlinarith only [hterm, hax, sq_nonneg a, sq_nonneg Y]
    _ ≤ 4 / 5 := by apply (div_le_iff₀ hx).2; linarith
