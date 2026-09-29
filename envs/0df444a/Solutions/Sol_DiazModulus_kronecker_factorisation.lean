-- Prove2me | solution 1 for DiazModulus.kronecker_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-19T18:41:49.963463+00:00
-- url     : https://prove2.me/submissions/d8b55a34-fed7-4f4e-b17c-54318f50a704

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace P7Kron

/-- `exp (w * (k * l)) = (exp w ^ k) ^ l` for natural `k, l`, with the casts arranged the way
the matrix entries present them. -/
lemma exp_mul_nat (w : ℂ) (k l : ℕ) :
    Complex.exp (w * ((k : ℂ) * (l : ℂ))) = (Complex.exp w ^ k) ^ l := by
  rw [← pow_mul, show w * ((k : ℂ) * (l : ℂ)) = ((k * l : ℕ) : ℂ) * w by push_cast; ring,
    Complex.exp_nat_mul]

/-- If `‖w‖ ≠ 1` then the powers `w ^ a` are pairwise distinct. The modulus does the
separating, so nothing about arguments is needed. -/
lemma pow_injective_of_norm_ne_one {w : ℂ} (hw : w ≠ 0) (h1 : ‖w‖ ≠ 1) (n : ℕ) :
    Function.Injective (fun a : Fin n => w ^ (a : ℕ)) := by
  have hpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hlog : Real.log ‖w‖ ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hpos h1
  intro a b hab
  have hnorm : ‖w‖ ^ (a : ℕ) = ‖w‖ ^ (b : ℕ) := by
    rw [← norm_pow, ← norm_pow]
    exact congrArg _ hab
  have hlogeq : ((a : ℕ) : ℝ) * Real.log ‖w‖ = ((b : ℕ) : ℝ) * Real.log ‖w‖ := by
    have := congrArg Real.log hnorm
    rwa [Real.log_pow, Real.log_pow] at this
  have hcast : ((a : ℕ) : ℝ) = ((b : ℕ) : ℝ) := mul_right_cancel₀ hlog hlogeq
  exact Fin.ext (Nat.cast_injective hcast)

end P7Kron

open DiazModulus in
theorem solution
    (u : ℂ) (hu : IsCandidate u) (hre : u.re ≠ 0) (N : ℕ)
    (M : Matrix (Fin (N + 1) × Fin (N + 1)) (Fin (N + 1) × Fin (N + 1)) ℂ)
    (hM : ∀ p q, M p q =
      Complex.exp (u * ((p.1 : ℕ) * (q.1 : ℕ)) + conj u * ((p.2 : ℕ) * (q.2 : ℕ))))
    (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (hA : ∀ a m, A a m = (Complex.exp u ^ (a : ℕ)) ^ (m : ℕ))
    (hB : ∀ b n, B b n = (conj (Complex.exp u) ^ (b : ℕ)) ^ (n : ℕ)) :
    M = Matrix.kroneckerMap (· * ·) A B ∧
      M.det = A.det ^ (N + 1) * B.det ^ (N + 1) ∧ M.det ≠ 0 := by
  -- `exp u ≠ 0`, and its modulus is not `1` because `Re u ≠ 0`
  have hα : Complex.exp u ≠ 0 := Complex.exp_ne_zero u
  have hαnorm : ‖Complex.exp u‖ ≠ 1 := by
    rw [Complex.norm_exp]
    intro h
    exact hre (Real.exp_injective (by rw [h, Real.exp_zero]))
  have hconj : ‖conj (Complex.exp u)‖ ≠ 1 := by
    rwa [RCLike.norm_conj]
  -- the factorisation, entry by entry
  have hfac : M = Matrix.kroneckerMap (· * ·) A B := by
    ext p q
    rw [hM, Matrix.kroneckerMap_apply, hA, hB, Complex.exp_add, P7Kron.exp_mul_nat,
      ← Complex.exp_conj, P7Kron.exp_mul_nat]
  refine ⟨hfac, ?_, ?_⟩
  · rw [hfac, Matrix.det_kronecker, Fintype.card_fin]
  -- non-vanishing: both factors are Vandermonde in pairwise distinct nodes
  · have hAv : A = Matrix.vandermonde (fun a : Fin (N + 1) => Complex.exp u ^ (a : ℕ)) := by
      ext a m
      rw [hA, Matrix.vandermonde_apply]
    have hBv : B = Matrix.vandermonde (fun b : Fin (N + 1) => conj (Complex.exp u) ^ (b : ℕ)) := by
      ext b n
      rw [hB, Matrix.vandermonde_apply]
    have hAdet : A.det ≠ 0 := by
      rw [hAv, Matrix.det_vandermonde_ne_zero_iff]
      exact P7Kron.pow_injective_of_norm_ne_one hα hαnorm _
    have hBdet : B.det ≠ 0 := by
      rw [hBv, Matrix.det_vandermonde_ne_zero_iff]
      exact P7Kron.pow_injective_of_norm_ne_one (by simp [hα]) hconj _
    rw [hfac, Matrix.det_kronecker]
    exact mul_ne_zero (pow_ne_zero _ hAdet) (pow_ne_zero _ hBdet)


#print axioms solution
