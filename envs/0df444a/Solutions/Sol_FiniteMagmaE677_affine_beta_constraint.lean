-- Prove2me | solution 1 for FiniteMagmaE677.affine_beta_constraint
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T17:20:19.767589+00:00
-- url     : https://prove2.me/submissions/33e64220-c07d-4a8e-9df8-408175409828

import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_FiniteMagmaE677

/-!
# The beta constraint: classification completeness for affine models

Let `R` be any commutative ring and suppose the affine operation
`x ⋄ y = a·x + b·y + c` satisfies E677. Evaluating the identity at the pairs
`(0,0)`, `(1,0)` and `(0,1)` extracts the three coefficient identities

  `C1 : a·b + a·b³ − 1 = 0`,  `C2 : a + a²·b² + b³ = 0`,
  `C3 : c·(a·b² + b² + b + 1) = 0`.

Eliminating `a` between `C1` and `C2` (multiply `C2` by `(b + b³)²` and
substitute `a·(b + b³) = 1`) gives the universal identity

  `(b + b³)²·C2 − (b + b³ + 2b²)·C1 − b²·C1² = b·Φ₁₀(b)·q₄(b)`,

where `Φ₁₀(b) = b⁴ − b³ + b² − b + 1` is the tenth cyclotomic polynomial and
`q₄(b) = b⁴ + b³ + 2b² + 2b + 1` is the Type II quartic. Hence

  `b·Φ₁₀(b)·q₄(b) = 0`.

Over a field (where `C1` forces `b ≠ 0`), every affine model falls into the
Type I branch `Φ₁₀(b) = 0` or the Type II branch `q₄(b) = 0` — the
completeness direction of the blueprint's classification of linear models
over finite fields, with `a = 1/(b + b³)` on either branch.
-/

universe v

theorem FiniteMagmaE677.affine_beta_constraint {R : Type v} [CommRing R] (a b c : R)
    (h : FiniteMagmaE677.E677 (fun x y : R => a * x + b * y + c)) :
    b * (b ^ 4 - b ^ 3 + b ^ 2 - b + 1) * (b ^ 4 + b ^ 3 + 2 * b ^ 2 + 2 * b + 1) = 0 := by
  -- extract the coefficient identities
  have h00 := h 0 0
  have h10 := h 1 0
  have h01 := h 0 1
  have hC3 : c * (a * b ^ 2 + b ^ 2 + b + 1) = 0 := by
    linear_combination -h00
  have hC1 : a * b + a * b ^ 3 - 1 = 0 := by
    linear_combination -h10 - hC3
  have hC2 : a + a ^ 2 * b ^ 2 + b ^ 3 = 0 := by
    linear_combination -h01 - hC3
  -- elimination identity (universal)
  have hP : (b + b ^ 3) ^ 2 * (a + a ^ 2 * b ^ 2 + b ^ 3)
      - (b + b ^ 3 + 2 * b ^ 2) * (a * b + a * b ^ 3 - 1)
      - b ^ 2 * (a * b + a * b ^ 3 - 1) ^ 2
      = b * (b ^ 4 - b ^ 3 + b ^ 2 - b + 1) * (b ^ 4 + b ^ 3 + 2 * b ^ 2 + 2 * b + 1) := by
    ring
  rw [hC2, hC1] at hP
  simp at hP
  exact hP.symm

theorem solution {R : Type v} [CommRing R] (a b c : R)
    (h : FiniteMagmaE677.E677 (fun x y : R => a * x + b * y + c)) :
    b * (b ^ 4 - b ^ 3 + b ^ 2 - b + 1) * (b ^ 4 + b ^ 3 + 2 * b ^ 2 + 2 * b + 1) = 0 :=
  FiniteMagmaE677.affine_beta_constraint a b c h
