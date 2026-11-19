-- Prove2me | solution 1 for DiazModulus.fischler_linear_pow_prod_mem
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-18T16:24:50.997997+00:00
-- url     : https://prove2.me/submissions/8199b444-2725-4445-a768-2717e8305eb9

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # Coefficients of a power of a linear form

Write `L = Σᵢ λᵢXᵢ`. We prove the more general claim: if every coefficient of `a·Lᵏ` lies in `ℒ̃`, then
`a·λ_{I(0)}⋯λ_{I(k−1)} ∈ ℒ̃` for every `I : {0, …, k−1} → {1, …, m}`; the statement is the case `a = 1`. The
proof is by induction on `k`. For `k = 0` the constant coefficient is `a`. For the step, differentiate in the
variable `X_{I(0)}`: `∂(a·L^{k+1}) = a(k + 1)λ_{I(0)}·Lᵏ`, and each coefficient of a partial derivative is a
natural multiple of a coefficient of the polynomial, so it lies in `ℒ̃` (a `Q̄`-vector space). The induction
hypothesis applied to `a(k + 1)λ_{I(0)}` and to the tail of `I` gives `(k + 1)·a·λ_I ∈ ℒ̃`, and dividing by the
non-zero algebraic number `k + 1` gives `a·λ_I ∈ ℒ̃`. -/

namespace RC9_F2
open DiazModulus MvPolynomial

/-- `∂ⱼ (Σᵢ λᵢ Xᵢ) = λⱼ`. -/
theorem pderiv_linear {m : ℕ} (Λ : Fin m → ℂ) (j : Fin m) :
    pderiv j (∑ i, C (Λ i) * X i : MvPolynomial (Fin m) ℂ) = C (Λ j) := by
  classical
  simp [map_sum, pderiv_X, Pi.single_apply]

/-- If every coefficient of `a · Lᵏ` lies in `ℒ̃`, then so does `a · λ_I` for every `I`. Induction on `k`,
differentiating once in the variable `I 0`. -/
theorem key {m : ℕ} (Λ : Fin m → ℂ) : ∀ (k : ℕ) (a : ℂ),
    (∀ s, (C a * (∑ i, C (Λ i) * X i) ^ k : MvPolynomial (Fin m) ℂ).coeff s ∈ LogAlgTilde) →
    ∀ I : Fin k → Fin m, a * ∏ t, Λ (I t) ∈ LogAlgTilde := by
  intro k
  induction k with
  | zero =>
    intro a h I
    simpa using h 0
  | succ k ih =>
    intro a h I
    set L : MvPolynomial (Fin m) ℂ := ∑ i, C (Λ i) * X i with hL
    have hd : pderiv (I 0) (C a * L ^ (k + 1)) = C (a * ((k + 1 : ℂ) * Λ (I 0))) * L ^ k := by
      rw [pderiv_C_mul, pderiv_pow, hL, pderiv_linear]
      simp only [map_mul, map_add, map_one, map_natCast, Nat.cast_add, Nat.cast_one,
        add_tsub_cancel_right]
      ring
    have h' : ∀ s, (C (a * ((k + 1 : ℂ) * Λ (I 0))) * L ^ k).coeff s ∈ LogAlgTilde := by
      intro s
      rw [← hd, coeff_pderiv]
      have := nsmul_mem (h (s + Finsupp.single (I 0) 1)) (s (I 0) + 1)
      rwa [nsmul_eq_mul, mul_comm, Nat.cast_add, Nat.cast_one] at this
    have hI := ih _ h' (Fin.tail I)
    have hk : ((k + 1 : ℕ) : ↥Qbar) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    rw [← Submodule.smul_mem_iff LogAlgTilde hk]
    convert hI using 1
    rw [Subfield.smul_def, smul_eq_mul, Fin.prod_univ_succ]
    simp only [Fin.tail, Nat.cast_add, Nat.cast_one]
    push_cast
    ring

end RC9_F2

open DiazModulus in
theorem solution {m k : ℕ} (Λ : Fin m → ℂ)
    (hP : ∀ s, ((∑ i, MvPolynomial.C (Λ i) * MvPolynomial.X i) ^ k :
      MvPolynomial (Fin m) ℂ).coeff s ∈ LogAlgTilde) :
    ∀ I : Fin k → Fin m, ∏ t, Λ (I t) ∈ LogAlgTilde := by
  intro I
  simpa using RC9_F2.key Λ k 1 (by simpa using hP) I
