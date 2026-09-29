-- Prove2me | solution 1 for BurauFaithful.burau_three_fullTwist_sq_infinite_order
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-29T06:07:49.637821+00:00
-- url     : https://prove2.me/submissions/751f001e-8263-4d61-ac2b-e22334256637

/-
Direct proof of `BurauFaithful.burau_three_fullTwist_sq_infinite_order` (Birman, *Braids, Links,
and Mapping Class Groups*, Ann. of Math. Studies 82, 1974, §3.3, Theorem 3.15, pp. 129--130:
"a calculation shows that the central element has infinite order").

Specialize the indeterminate at $t = 2$ into $\mathbb{Q}$: the determinant of the Burau matrix of
$\sigma_1\sigma_2$ is $t^2$, hence becomes $4$, while the determinant of the $(6k)$-th power of
that matrix is $1$; so $4^{6k} = 1$ and hence $k = 0$.

This file is self-contained: it imports the definition of the Burau representation and computes
the explicit matrix of $\rho_3(\sigma_1\sigma_2)$ over $\mathbb{Z}[t,t^{-1}]$ from that definition.
-/
import Definitions.Def_BurauFaithful_UnreducedBurau

set_option autoImplicit false

open LaurentPolynomial Matrix BraidsLinksMCG

/-- The specialization `ℤ[t,t⁻¹] → ℚ`, `t ↦ 2`. -/
noncomputable def specTwo : (LaurentPolynomial ℤ) →+* ℚ :=
  LaurentPolynomial.eval₂ (Int.castRingHom ℚ) (Units.mk0 (2 : ℚ) (by norm_num))

/-- **Birman, §3.3 (second step of Theorem 3.15).** The image of the square of the full twist,
`Δ⁴ = (σ₁σ₂)⁶`, under the unreduced Burau representation `ρ₃` has infinite order. -/
theorem solution (k : ℤ) :
    (BurauFaithful.burauRep 3 (BraidsLinksMCG.sigma ⟨0, by decide⟩ *
        BraidsLinksMCG.sigma ⟨1, by decide⟩)) ^ (6 * k) = 1 → k = 0 := by
  intro h
  set M : GL (Fin 3) (LaurentPolynomial ℤ) :=
    BurauFaithful.burauRep 3 (BraidsLinksMCG.sigma ⟨0, by decide⟩ *
      BraidsLinksMCG.sigma ⟨1, by decide⟩) with hM
  have hM' : M ^ (6 * k) = 1 := by
    rw [hM]
    exact h
  -- the Burau matrix of `σ₁σ₂` over `ℤ[t,t⁻¹]`
  have hsym : (↑(BurauFaithful.burauRep 3 (BraidsLinksMCG.sigma ⟨0, by decide⟩ *
        BraidsLinksMCG.sigma ⟨1, by decide⟩)) :
      Matrix (Fin 3) (Fin 3) (LaurentPolynomial ℤ)) =
      ![![1 - LaurentPolynomial.T 1,
          LaurentPolynomial.T 1 * (1 - LaurentPolynomial.T 1),
          LaurentPolynomial.T 1 ^ 2],
        ![1, 0, 0],
        ![0, 1, 0]] := by
    simp only [map_mul, Units.val_mul]
    have hg : ∀ i : Fin (3 - 1),
        (BurauFaithful.burauRep 3 (BraidsLinksMCG.sigma i)).1 = BurauFaithful.burauMatrix i := by
      intro i
      have hh := PresentedGroup.toGroup.of (h := BurauFaithful.burauGen_relations 3) (x := i)
      exact congrArg Units.val hh
    rw [hg, hg]
    refine Matrix.ext fun a b => ?_
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, BurauFaithful.burauMatrix_apply] <;>
      first | ring1 | (simp; done) | (left; ring1) |
        (rw [← LaurentPolynomial.T_add]; norm_num; done)
  -- the specialized matrix, entrywise
  have hmat : (Matrix.GeneralLinearGroup.map specTwo M : Matrix (Fin 3) (Fin 3) ℚ) =
      !![ -1, -2, 4;
          1,  0, 0;
          0,  1, 0 ] := by
    ext i j
    rw [Matrix.GeneralLinearGroup.map_apply, hM, hsym]
    fin_cases i <;> fin_cases j <;>
      simp [specTwo, LaurentPolynomial.eval₂_T] <;> norm_num
  -- its determinant is 4 = 2²
  have hdet4 : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map specTwo M) : ℚˣ) :
      ℚ) = 4 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hmat, Matrix.det_fin_three]
    simp
  -- the determinant of the (6k)-th power is 1, hence 4^(6k) = 1
  have hmap : (Matrix.GeneralLinearGroup.map specTwo M) ^ (6 * k) = 1 := by
    rw [← map_zpow, hM', map_one]
  have hdet : (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map specTwo M)) ^ (6 * k) =
      1 := by
    rw [← map_zpow, hmap, map_one]
  have h4 : (4 : ℚ) ^ (6 * k) = 1 := by
    have hval := congrArg (fun u : ℚˣ => (u : ℚ)) hdet
    rw [Units.val_zpow_eq_zpow_val, hdet4, Units.val_one] at hval
    exact hval
  -- 4 has infinite multiplicative order
  have hinj : Function.Injective (fun n : ℤ => (4 : ℚ) ^ n) :=
    (zpow_right_strictMono₀ (show (1 : ℚ) < 4 by norm_num)).injective
  have h6k : 6 * k = 0 := hinj (by simpa using h4)
  exact (mul_eq_zero.mp h6k).resolve_left (by norm_num)
