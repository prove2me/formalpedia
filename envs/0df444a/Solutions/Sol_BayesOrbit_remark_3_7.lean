-- Prove2me | solution 1 for BayesOrbit.remark_3_7
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:37:30.214985+00:00
-- url     : https://prove2.me/submissions/2d6fdbb3-bffd-44cd-896a-8fc63baeb997

import Mathlib

open scoped BigOperators
namespace BayesOrbit

/-- Remark 3.7 of Hellman–Levy, Dense Orbits of the Bayesian Updating Group Action, accepted
manuscript (Enlighten 227272), p.16 (PDF 17), extended. For a square matrix `A` with algebraically
independent entries: (3.10), already for a single row `l`, forces `r = 0`, as printed; moreover
`det A ≠ 0`, and for `θ` with `A θ = 1` (the all-ones vector) an integer vector `w` with
`∑ i, w i * θ i ∈ ℤ` is `0`.

**Formalization Note.** Algebraic independence is over `ℚ`, of the family indexed by `I × I`. The
index `l` is free in the printed (3.10); the first clause holds for each row, so it covers the
reading "for all `l`" as well. The other two clauses are the instance of the integrality condition
of `theorem_3_4` that the proof of Lemma 3.8 needs in place of the printed clause: `θ` as a single
column, which is what yields one integer `d` common to all rows. -/
theorem _root_.solution {I : Type*} [Fintype I] [DecidableEq I] (A : Matrix I I ℝ)
    (hA : AlgebraicIndependent ℚ (fun x : I × I => A x.1 x.2)) :
    (∀ (l : I) (r : I → ℤ), (∃ z : ℤ, ∑ i, A l i * (r i : ℝ) = (z : ℝ)) → r = 0) ∧
    A.det ≠ 0 ∧
    ∀ θ : I → ℝ, A.mulVec θ = 1 →
      ∀ w : I → ℤ, (∃ z : ℤ, ∑ i, (w i : ℝ) * θ i = (z : ℝ)) → w = 0 := by
  classical
  have hzero : ∀ p : MvPolynomial (I × I) ℚ, MvPolynomial.aeval (fun x : I × I => A x.1 x.2) p = 0 → p = 0 :=
    fun p hp => (algebraicIndependent_iff.1 hA) p hp
  set X : Matrix I I (MvPolynomial (I × I) ℚ) := fun i j => MvPolynomial.X (i, j) with hX
  have hmapA : (MvPolynomial.aeval (fun x : I × I => A x.1 x.2) : MvPolynomial (I × I) ℚ →ₐ[ℚ] ℝ).toRingHom.mapMatrix X = A := by
    ext i j
    show MvPolynomial.aeval (fun x : I × I => A x.1 x.2) (MvPolynomial.X (i, j)) = A i j
    exact MvPolynomial.aeval_X _ _
  have hdetA : MvPolynomial.aeval (fun x : I × I => A x.1 x.2) X.det = A.det := by
    have := RingHom.map_det (MvPolynomial.aeval (fun x : I × I => A x.1 x.2) : MvPolynomial (I × I) ℚ →ₐ[ℚ] ℝ).toRingHom X
    rw [hmapA] at this; exact this
  have hmapB : ∀ B : Matrix I I ℚ, (MvPolynomial.eval (fun x : I × I => B x.1 x.2)).mapMatrix X = B := by
    intro B; ext i j
    show MvPolynomial.eval (fun x : I × I => B x.1 x.2) (MvPolynomial.X (i, j)) = B i j
    exact MvPolynomial.eval_X _
  have hdetB : ∀ B : Matrix I I ℚ, MvPolynomial.eval (fun x : I × I => B x.1 x.2) X.det = B.det := by
    intro B
    have := RingHom.map_det (MvPolynomial.eval (fun x : I × I => B x.1 x.2)) X
    rw [hmapB] at this; exact this
  have hXdet : X.det ≠ 0 := by
    intro h
    have := hdetB 1
    rw [h, map_zero, Matrix.det_one] at this
    exact zero_ne_one this
  have hdet : A.det ≠ 0 := by
    intro h
    exact hXdet (hzero _ (by rw [hdetA, h]))
  refine ⟨?_, hdet, ?_⟩
  · intro l r ⟨z, hz⟩
    set p : MvPolynomial (I × I) ℚ := ∑ i, MvPolynomial.C (r i : ℚ) * MvPolynomial.X (l, i) - MvPolynomial.C (z : ℚ) with hp
    have hp0 : p = 0 := by
      refine hzero p ?_
      simp only [hp, map_sub, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, map_intCast]
      rw [sub_eq_zero, ← hz]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hev : ∀ B : I × I → ℚ, ∑ i, (r i : ℚ) * B (l, i) = (z : ℚ) := by
      intro B
      have := congrArg (MvPolynomial.eval B) hp0
      simpa [hp, sub_eq_zero] using this
    have hz0 : (z : ℚ) = 0 := by
      have := hev 0; simpa using this.symm
    funext k
    have := hev (fun x => if x = (l, k) then 1 else 0)
    rw [hz0] at this
    simp only [Prod.mk.injEq, true_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    exact_mod_cast this
  · intro θ hθ w ⟨z, hz⟩
    set q : MvPolynomial (I × I) ℚ := ∑ i, MvPolynomial.C (w i : ℚ) * (X.adjugate.mulVec 1) i - MvPolynomial.C (z : ℚ) * X.det with hq
    have hadjA : (MvPolynomial.aeval (fun x : I × I => A x.1 x.2) : MvPolynomial (I × I) ℚ →ₐ[ℚ] ℝ).toRingHom.mapMatrix X.adjugate = A.adjugate := by
      rw [RingHom.map_adjugate, hmapA]
    have hθ' : A.adjugate.mulVec 1 = A.det • θ := by
      rw [← hθ, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hq0 : q = 0 := by
      refine hzero q ?_
      have h1 : ∀ i, MvPolynomial.aeval (fun x : I × I => A x.1 x.2) ((X.adjugate.mulVec 1) i) = A.det * θ i := by
        intro i
        have hi : MvPolynomial.aeval (fun x : I × I => A x.1 x.2) ((X.adjugate.mulVec 1) i) = (A.adjugate.mulVec 1) i := by
          rw [← hadjA]
          simp [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply]
        rw [hi, hθ']; rfl
      simp only [hq, map_sub, map_sum, map_mul, MvPolynomial.aeval_C, map_intCast, h1, hdetA]
      rw [sub_eq_zero, ← hz, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hev : ∀ (B : Matrix I I ℚ) (φ : I → ℚ), B.mulVec φ = 1 → B.det ≠ 0 → ∑ i, (w i : ℚ) * φ i = (z : ℚ) := by
      intro B φ hφ hB
      have hadjB : (MvPolynomial.eval (fun x : I × I => B x.1 x.2)).mapMatrix X.adjugate = B.adjugate := by
        rw [RingHom.map_adjugate, hmapB]
      have hφ' : B.adjugate.mulVec 1 = B.det • φ := by
        rw [← hφ, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
      have h1 : ∀ i, MvPolynomial.eval (fun x : I × I => B x.1 x.2) ((X.adjugate.mulVec 1) i) = B.det * φ i := by
        intro i
        have hi : MvPolynomial.eval (fun x : I × I => B x.1 x.2) ((X.adjugate.mulVec 1) i) = (B.adjugate.mulVec 1) i := by
          rw [← hadjB]
          simp [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply]
        rw [hi, hφ']; rfl
      have := congrArg (MvPolynomial.eval (fun x : I × I => B x.1 x.2)) hq0
      simp only [hq, map_sub, map_sum, map_mul, MvPolynomial.eval_C, h1, hdetB, map_zero, sub_eq_zero] at this
      apply mul_left_cancel₀ hB
      rw [mul_comm B.det (z : ℚ), ← this, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hdiag : ∀ d : I → ℚ, (∀ i, d i ≠ 0) → ∑ i, (w i : ℚ) * (d i)⁻¹ = (z : ℚ) := by
      intro d hd
      refine hev (Matrix.diagonal d) (fun i => (d i)⁻¹) ?_ ?_
      · funext i; rw [Matrix.mulVec_diagonal]; exact mul_inv_cancel₀ (hd i)
      · rw [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.2 fun i _ => hd i
    funext k
    have h1 := hdiag (fun _ => 1) (fun _ => one_ne_zero)
    have h2 := hdiag (fun i => if i = k then 2 else 1) (fun i => by split <;> norm_num)
    have e : ∀ i, (w i : ℚ) * (if i = k then (2:ℚ) else 1)⁻¹ = (w i : ℚ) * 1⁻¹ - (if i = k then (w i : ℚ) / 2 else 0) := by
      intro i; split <;> ring
    simp only [e, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
    rw [h1] at h2
    have : (w k : ℚ) = 0 := by linarith
    exact_mod_cast this


end BayesOrbit

