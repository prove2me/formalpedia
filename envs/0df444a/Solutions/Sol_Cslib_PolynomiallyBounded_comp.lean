-- Prove2me | solution 1 for Cslib.PolynomiallyBounded.comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T01:02:22.260398+00:00
-- url     : https://prove2.me/submissions/b7769a37-17f9-47b4-b9e8-80b847a62586

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
    PolynomiallyBounded (fun n => f (g n)) := by
  obtain ⟨c, d, hf⟩ := polynomiallyBounded_iff_le.1 hf
  obtain ⟨c', d', hg⟩ := polynomiallyBounded_iff_le.1 hg
  refine of_forall_le (c * (c' + 1) ^ d) (d' * d) fun n => ?_
  have hsize : g n + 1 ≤ (c' + 1) * (n + 1) ^ d' := by
    have hp : 1 ≤ (n + 1) ^ d' := Nat.one_le_pow _ _ (by omega)
    calc
      g n + 1 ≤ c' * (n + 1) ^ d' + (n + 1) ^ d' := Nat.add_le_add (hg n) hp
      _ = (c' + 1) * (n + 1) ^ d' := by ring
  calc
    f (g n) ≤ c * (g n + 1) ^ d := hf (g n)
    _ ≤ c * ((c' + 1) * (n + 1) ^ d') ^ d :=
      Nat.mul_le_mul_left c (Nat.pow_le_pow_left hsize d)
    _ = c * (c' + 1) ^ d * (n + 1) ^ (d' * d) := by rw [mul_pow, pow_mul, mul_assoc]
