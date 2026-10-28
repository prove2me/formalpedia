-- Prove2me | solution 1 for Cslib.PolynomiallyBounded.mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T00:59:52.038394+00:00
-- url     : https://prove2.me/submissions/7c3afa80-24e6-4f7a-b557-a1877d4804f6

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

theorem solution (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => f n * g n) := by
  obtain ⟨c, d, hf⟩ := polynomiallyBounded_iff_le.1 hf
  obtain ⟨c', d', hg⟩ := polynomiallyBounded_iff_le.1 hg
  refine of_forall_le (c * c') (d + d') fun n => ?_
  calc
    f n * g n ≤ (c * (n + 1) ^ d) * (c' * (n + 1) ^ d') := Nat.mul_le_mul (hf n) (hg n)
    _ = (c * c') * (n + 1) ^ (d + d') := by rw [pow_add]; ring
