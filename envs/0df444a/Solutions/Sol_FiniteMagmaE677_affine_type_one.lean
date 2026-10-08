-- Prove2me | solution 1 for FiniteMagmaE677.affine_type_one
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T17:09:51.379853+00:00
-- url     : https://prove2.me/submissions/18b572d1-537f-4506-850a-9e7b79f3cac3

import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.LinearCombination
import Definitions.Def_FiniteMagmaE677

/-!
# Soundness of the affine Type I model family

For an affine operation `x ⋄ y = a·x + b·y + c` over a commutative ring, the
E677 identity `x = y ⋄ (x ⋄ ((y ⋄ x) ⋄ y))` expands to a polynomial identity
whose right side is `(a·b + a·b³)·x + (a + a²·b² + b³)·y + c·(a·b² + b² + b + 1)`.
For the blueprint's Type I family `a = 1 − β`, `c = 0` with
`β⁴ − β³ + β² − β + 1 = 0` (β a primitive tenth root of unity; e.g. `β = 2`
in `𝔽₅`, giving `x ⋄ y = 2x − y`), the two coefficient identities are
exactly `±Φ₁₀(β)`, so E677 holds. Combined with `affine_magma_e255`, every
Type I model over a finite ring satisfies both E677 and E255.
-/

universe v

theorem FiniteMagmaE677.affine_type_one {F : Type v} [CommRing F] (β : F)
    (h : β ^ 4 - β ^ 3 + β ^ 2 - β + 1 = 0) :
    FiniteMagmaE677.E677 (fun x y : F => (1 - β) * x + β * y) := by
  intro x y
  have e1 : (1 - β) * β + (1 - β) * β ^ 3 - 1 = 0 := by
    linear_combination -h
  have e2 : (1 - β) + (1 - β) ^ 2 * β ^ 2 + β ^ 3 = 0 := by
    linear_combination h
  linear_combination (-x) * e1 + (-y) * e2

theorem solution {F : Type v} [CommRing F] (β : F)
    (h : β ^ 4 - β ^ 3 + β ^ 2 - β + 1 = 0) :
    FiniteMagmaE677.E677 (fun x y : F => (1 - β) * x + β * y) :=
  FiniteMagmaE677.affine_type_one β h
