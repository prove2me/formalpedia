-- Prove2me | solution 1 for DiazModulus.no_first_order_arithmetic_operator
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-19T18:41:56.470772+00:00
-- url     : https://prove2.me/submissions/d0297c1c-7714-4b77-ac36-999577ca773d

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace P7Deriv

open DiazModulus

/-- A polynomial with algebraic coefficients takes algebraic values at algebraic points.
Proved through the subfield `Qbar`, which is closed under the finite sums and products that
`MvPolynomial.eval` unfolds to. -/
lemma eval_mem_Qbar {σ : Type*} (p : MvPolynomial σ ℂ) (x : σ → ℂ)
    (hc : ∀ d, MvPolynomial.coeff d p ∈ Qbar) (hx : ∀ i, x i ∈ Qbar) :
    MvPolynomial.eval x p ∈ Qbar := by
  rw [MvPolynomial.eval_eq]
  refine Subfield.sum_mem _ fun d _ => mul_mem (hc d) ?_
  exact Subfield.prod_mem _ fun i _ => pow_mem (hx i) _

/-- An integer is algebraic over `ℚ`. Proved from the polynomial rather than through a library
alias, because the alias was renamed between the two Mathlib revisions this has to build on. -/
lemma int_isAlgebraic (m : ℤ) : IsAlgebraic ℚ ((m : ℂ)) := by
  refine ⟨Polynomial.X - Polynomial.C (m : ℚ), Polynomial.X_sub_C_ne_zero _, ?_⟩
  simp

/-- Complex conjugation preserves algebraicity over `ℚ`. -/
lemma conj_isAlgebraic {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (conj z) := by
  have hi : Function.Injective (Complex.conjAe.restrictScalars ℚ) := Complex.conjAe.injective
  exact (isAlgebraic_algHom_iff (Complex.conjAe.restrictScalars ℚ).toAlgHom hi).mpr h

/-- The values of `F (z,w) = exp (u z + conj u w)` on `ℤ²` are algebraic and non-zero. -/
lemma value_mem_Qbar {u : ℂ} (hu : IsAlgebraic ℚ (Complex.exp u)) (m n : ℤ) :
    Complex.exp (u * m + conj u * n) ∈ Qbar := by
  have h1 : Complex.exp (u * m) = Complex.exp u ^ m := by
    rw [mul_comm, Complex.exp_int_mul]
  have h2 : Complex.exp (conj u * n) = conj (Complex.exp u) ^ n := by
    rw [mul_comm, Complex.exp_int_mul, Complex.exp_conj]
  rw [Complex.exp_add, h1, h2]
  exact mul_mem (zpow_mem (mem_Qbar_iff.mpr hu) m)
    (zpow_mem (mem_Qbar_iff.mpr (conj_isAlgebraic hu)) n)

end P7Deriv

open DiazModulus in
theorem solution
    (u : ℂ) (hu : IsCandidate u)
    (hbaker : ∀ p q : ℂ, IsAlgebraic ℚ p → IsAlgebraic ℚ q →
        IsAlgebraic ℚ (p * u + q * conj u) → p = 0 ∧ q = 0)
    (a b : MvPolynomial (Fin 2) ℂ)
    (ha : ∀ d, IsAlgebraic ℚ (MvPolynomial.coeff d a))
    (hb : ∀ d, IsAlgebraic ℚ (MvPolynomial.coeff d b))
    (hvalues : ∀ m n : ℤ,
        IsAlgebraic ℚ
          ((MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (m : ℂ) else (n : ℂ)) a * u
              + MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (m : ℂ) else (n : ℂ)) b * conj u)
            * Complex.exp (u * m + conj u * n))) :
    a = 0 ∧ b = 0 := by
  -- both polynomials vanish at every integer point
  have key : ∀ m n : ℤ,
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (m : ℂ) else (n : ℂ)) a = 0 ∧
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (m : ℂ) else (n : ℂ)) b = 0 := by
    intro m n
    have hxQ : ∀ i : Fin 2, (if i = 0 then (m : ℂ) else (n : ℂ)) ∈ Qbar := by
      intro i
      by_cases h : i = 0
      · simp only [h]
        exact mem_Qbar_iff.mpr (P7Deriv.int_isAlgebraic m)
      · simp only [h]
        exact mem_Qbar_iff.mpr (P7Deriv.int_isAlgebraic n)
    have hA : IsAlgebraic ℚ
        (MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (m : ℂ) else (n : ℂ)) a) :=
      mem_Qbar_iff.mp (P7Deriv.eval_mem_Qbar a _ (fun d => mem_Qbar_iff.mpr (ha d)) hxQ)
    have hB : IsAlgebraic ℚ
        (MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (m : ℂ) else (n : ℂ)) b) :=
      mem_Qbar_iff.mp (P7Deriv.eval_mem_Qbar b _ (fun d => mem_Qbar_iff.mpr (hb d)) hxQ)
    -- the exponential factor is algebraic and non-zero, so it can be divided out
    have hE : Complex.exp (u * m + conj u * n) ∈ Qbar :=
      P7Deriv.value_mem_Qbar hu.2.2 m n
    have hE0 : Complex.exp (u * m + conj u * n) ≠ 0 := Complex.exp_ne_zero _
    have hcomb : IsAlgebraic ℚ
        (MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (m : ℂ) else (n : ℂ)) a * u
          + MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (m : ℂ) else (n : ℂ)) b * conj u) := by
      have hprod : _ ∈ Qbar := mem_Qbar_iff.mpr (hvalues m n)
      have := div_mem hprod hE
      rwa [mul_div_assoc, div_self hE0, mul_one, mem_Qbar_iff] at this
    exact hbaker _ _ hA hB hcomb
  -- a polynomial vanishing on all of `ℤ²` is zero
  have hinf : ∀ _i : Fin 2, (Set.range (fun k : ℤ => (k : ℂ))).Infinite := fun _ =>
    Set.infinite_range_of_injective fun p q h => by exact_mod_cast h
  have step : ∀ p : MvPolynomial (Fin 2) ℂ,
      (∀ m n : ℤ,
        MvPolynomial.eval (fun i : Fin 2 => if i = 0 then (m : ℂ) else (n : ℂ)) p = 0) →
      p = 0 := by
    intro p hp
    refine MvPolynomial.funext_set (fun _ => Set.range (fun k : ℤ => (k : ℂ))) hinf ?_
    intro x hx
    obtain ⟨m, hm⟩ := hx 0 (Set.mem_univ 0)
    obtain ⟨n, hn⟩ := hx 1 (Set.mem_univ 1)
    have hxeq : x = fun i : Fin 2 => if i = 0 then (m : ℂ) else (n : ℂ) := by
      funext i
      fin_cases i
      · simpa using hm.symm
      · simpa using hn.symm
    rw [hxeq, hp m n, map_zero]
  exact ⟨step a fun m n => (key m n).1, step b fun m n => (key m n).2⟩


#print axioms solution
