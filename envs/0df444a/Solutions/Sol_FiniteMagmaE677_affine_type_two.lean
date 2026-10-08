-- Prove2me | solution 1 for FiniteMagmaE677.affine_type_two
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T17:09:52.066961+00:00
-- url     : https://prove2.me/submissions/da8a9ba6-c2ba-4aa1-a9ce-b6a7eeb43dad

import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.LinearCombination
import Definitions.Def_FiniteMagmaE677

/-!
# Soundness of the affine Type II model family

For an affine operation `x ⋄ y = a·x + b·y + c` over a commutative ring, the
E677 identity expands to a polynomial identity with right side
`(a·b + a·b³)·x + (a + a²·b² + b³)·y + c·(a·b² + b² + b + 1)`. For the
blueprint's Type II family (e.g. `a = 4, b = 3` in `𝔽₇`, or the exceptional
translation-invariant family `5x − 4y + c` on `𝔽₃₁`), it suffices to assume

  `b³ + b + 1 + a = 0`  and  `b⁴ + b³ + 2b² + 2b + 1 = 0`

with `c` arbitrary: these two relations imply all three coefficient
identities (and also `a² + a + 1 = 0`, the primitive-cube-root condition
stated in the blueprint). Combined with `affine_magma_e255`, every Type II
model over a finite ring satisfies both E677 and E255.
-/

universe v

theorem FiniteMagmaE677.affine_type_two {F : Type v} [CommRing F] (a b c : F)
    (h2 : b ^ 3 + b + 1 + a = 0) (h3 : b ^ 4 + b ^ 3 + 2 * b ^ 2 + 2 * b + 1 = 0) :
    FiniteMagmaE677.E677 (fun x y : F => a * x + b * y + c) := by
  intro x y
  have e1 : a * b + a * b ^ 3 - 1 = 0 := by
    linear_combination (b ^ 3 + b) * h2 + (-(b ^ 2) + b - 1) * h3
  have e2 : a + a ^ 2 * b ^ 2 + b ^ 3 = 0 := by
    linear_combination (a * b ^ 2 - b ^ 5 - b ^ 3 - b ^ 2 + 1) * h2
      + (b ^ 4 - b ^ 3 + b ^ 2 + b - 1) * h3
  have e3 : a * b ^ 2 + b ^ 2 + b + 1 = 0 := by
    linear_combination b ^ 2 * h2 + (1 - b) * h3
  linear_combination (-x) * e1 + (-y) * e2 + (-c) * e3

theorem solution {F : Type v} [CommRing F] (a b c : F)
    (h2 : b ^ 3 + b + 1 + a = 0) (h3 : b ^ 4 + b ^ 3 + 2 * b ^ 2 + 2 * b + 1 = 0) :
    FiniteMagmaE677.E677 (fun x y : F => a * x + b * y + c) :=
  FiniteMagmaE677.affine_type_two a b c h2 h3
