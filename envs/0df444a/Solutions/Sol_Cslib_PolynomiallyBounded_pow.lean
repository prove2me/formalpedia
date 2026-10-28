-- Prove2me | solution 1 for Cslib.PolynomiallyBounded.pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T01:01:34.111992+00:00
-- url     : https://prove2.me/submissions/248b0111-2c3d-4fdc-a946-c2521cdcc758

import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Common
import Mathlib.Tactic.FunProp
import Definitions.Def_CSLib_PolynomialGrowth
import Theorems.Thm_Cslib_polynomiallyBounded_iff_le

open Filter Cslib
variable {f g : ℕ → ℕ}

namespace Cslib.PolynomiallyBounded
theorem of_forall_le (c d : ℕ) (h : ∀ n, f n ≤ c * (n + 1) ^ d) : PolynomiallyBounded f :=
  polynomiallyBounded_iff_le.2 ⟨c, d, h⟩

end Cslib.PolynomiallyBounded
open Cslib.PolynomiallyBounded

theorem solution (hf : PolynomiallyBounded f) (d : ℕ) :
    PolynomiallyBounded (fun n => f n ^ d) := by
  obtain ⟨c, e, hf⟩ := polynomiallyBounded_iff_le.1 hf
  refine of_forall_le (c ^ d) (e * d) fun n => ?_
  calc
    f n ^ d ≤ (c * (n + 1) ^ e) ^ d := Nat.pow_le_pow_left (hf n) d
    _ = c ^ d * (n + 1) ^ (e * d) := by rw [mul_pow, pow_mul]
