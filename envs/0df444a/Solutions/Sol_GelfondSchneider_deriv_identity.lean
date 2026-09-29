-- Prove2me | solution 1 for GelfondSchneider.deriv_identity
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:06:22.437968+00:00
-- url     : https://prove2.me/submissions/37558649-109b-4d94-9daf-e66b08140554

import Mathlib

open NumberField

namespace GS_deriv

-- One exponential term: `d/dz (c · w^k · e^{wz}) = c · w^(k+1) · e^{wz}`.
lemma hasDerivAt_const_mul_exp (c w : ℂ) (k : ℕ) (z : ℂ) :
    HasDerivAt (fun z : ℂ => c * w ^ k * Complex.exp (w * z))
      (c * w ^ (k + 1) * Complex.exp (w * z)) z := by
  have h1 : HasDerivAt (fun z : ℂ => w * z) w z := by
    simpa using (hasDerivAt_id z).const_mul w
  have h2 := h1.cexp.const_mul (c * w ^ k)
  rw [show c * w ^ (k + 1) * Complex.exp (w * z) = c * w ^ k * (Complex.exp (w * z) * w) by ring]
  exact h2

-- Term-by-term derivative of a double exponential sum.
lemma hasDerivAt_sum_sum {q : ℕ} (c w : Fin q → Fin q → ℂ) (k : ℕ) (z : ℂ) :
    HasDerivAt (fun z : ℂ => ∑ a : Fin q, ∑ b : Fin q, c a b * w a b ^ k * Complex.exp (w a b * z))
      (∑ a : Fin q, ∑ b : Fin q, c a b * w a b ^ (k + 1) * Complex.exp (w a b * z)) z := by
  apply HasDerivAt.fun_sum
  intro a _
  apply HasDerivAt.fun_sum
  intro b _
  exact hasDerivAt_const_mul_exp (c a b) (w a b) k z

-- `k`-th derivative of a double exponential sum, as a function.
lemma iteratedDeriv_sum_sum {q : ℕ} (c w : Fin q → Fin q → ℂ) (k : ℕ) :
    iteratedDeriv k (fun z : ℂ => ∑ a : Fin q, ∑ b : Fin q, c a b * Complex.exp (w a b * z)) =
      fun z => ∑ a : Fin q, ∑ b : Fin q, c a b * w a b ^ k * Complex.exp (w a b * z) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    exact (hasDerivAt_sum_sum c w k z).deriv

-- The value of one exponential at an integer point, in terms of `e^l` and `e^{βl}`.
lemma exp_at_nat (β l : ℂ) (a b j : ℕ) :
    Complex.exp ((((a : ℂ) + 1) + ((b : ℂ) + 1) * β) * l * (j : ℂ)) =
      Complex.exp l ^ ((a + 1) * j) * Complex.exp (β * l) ^ ((b + 1) * j) := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

-- The image under `σ` of one summand on the right-hand side.
lemma map_term {K : Type*} [Field K] (σ : K →+* ℂ) (α' β' γ' : K) (l β : ℂ)
    (hβ : σ β' = β) (hα : σ α' = Complex.exp l) (hγ : σ γ' = Complex.exp (β * l))
    (e : K) (a b k j : ℕ) :
    σ (e * (((a : K) + 1) + ((b : K) + 1) * β') ^ k * α' ^ ((a + 1) * j) * γ' ^ ((b + 1) * j)) =
      σ e * (((a : ℂ) + 1) + ((b : ℂ) + 1) * β) ^ k *
        Complex.exp l ^ ((a + 1) * j) * Complex.exp (β * l) ^ ((b + 1) * j) := by
  simp only [map_mul, map_pow, map_add, map_natCast, map_one, hβ, hα, hγ]

end GS_deriv

open GS_deriv in
theorem solution (K : Type*) [Field K] (σ : K →+* ℂ) (α' β' γ' : K) (l β : ℂ)
    (hβ : σ β' = β) (hα : σ α' = Complex.exp l) (hγ : σ γ' = Complex.exp (β * l))
    (q : ℕ) (η : Fin q → Fin q → K) (k j : ℕ) :
    iteratedDeriv k (fun z : ℂ => ∑ a : Fin q, ∑ b : Fin q,
        σ (η a b) * Complex.exp ((((a : ℕ) + 1 : ℂ) + ((b : ℕ) + 1 : ℂ) * β) * l * z)) (j : ℂ) =
      l ^ k * σ (∑ a : Fin q, ∑ b : Fin q, η a b *
        (((a : ℕ) + 1 : K) + ((b : ℕ) + 1 : K) * β') ^ k *
        α' ^ (((a : ℕ) + 1) * j) * γ' ^ (((b : ℕ) + 1) * j)) := by
  rw [iteratedDeriv_sum_sum (fun a b => σ (η a b))
    (fun a b => (((a : ℕ) + 1 : ℂ) + ((b : ℕ) + 1 : ℂ) * β) * l) k]
  simp only [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [map_term σ α' β' γ' l β hβ hα hγ, exp_at_nat, mul_pow]
  ring

#print axioms solution
