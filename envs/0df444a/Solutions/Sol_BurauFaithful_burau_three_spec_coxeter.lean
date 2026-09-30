-- Prove2me | solution 1 for BurauFaithful.burau_three_spec_coxeter
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-29T15:41:30.417515+00:00
-- url     : https://prove2.me/submissions/d1710f90-eeab-45c5-921c-919c4a1eb5cc

/-
`BurauFaithful.burau_three_spec_coxeter`: the Coxeter relation of the modular group, realized by
the Burau matrices at `t = -1`: the fourth power of the specialized matrix of `σ₁σ₂σ₁` is `1`
(Birman, §3.3, Theorem 3.15, pp. 129--130, citing Moser--Coxeter 1964, p. 85).
-/
import Definitions.Def_BurauFaithful_UnreducedBurau
import Theorems.Thm_BurauFaithful_burauRep3_x

set_option autoImplicit false

open LaurentPolynomial Matrix BraidsLinksMCG

/-- The specialization `ℤ[t,t⁻¹] → ℤ`, `t ↦ -1`. -/
noncomputable def specM1 : (LaurentPolynomial ℤ) →+* ℤ :=
  LaurentPolynomial.eval₂ (Int.castRingHom ℤ) (-1 : ℤˣ)

theorem solution :
    (Matrix.GeneralLinearGroup.map specM1
      (BurauFaithful.burauRep 3 (BraidsLinksMCG.sigma ⟨0, by decide⟩ *
        BraidsLinksMCG.sigma ⟨1, by decide⟩ * BraidsLinksMCG.sigma ⟨0, by decide⟩))) ^ 4 =
      1 := by
  have hmat : (Matrix.GeneralLinearGroup.map specM1
      (BurauFaithful.burauRep 3 (BraidsLinksMCG.sigma ⟨0, by decide⟩ *
        BraidsLinksMCG.sigma ⟨1, by decide⟩ * BraidsLinksMCG.sigma ⟨0, by decide⟩)) :
        Matrix (Fin 3) (Fin 3) ℤ) =
      !![ 2, -2, 1;
          2, -1, 0;
          1,  0, 0 ] := by
    ext i j
    rw [Matrix.GeneralLinearGroup.map_apply]
    rw [show (↑(BurauFaithful.burauRep 3 (BraidsLinksMCG.sigma ⟨0, by decide⟩ *
          BraidsLinksMCG.sigma ⟨1, by decide⟩ * BraidsLinksMCG.sigma ⟨0, by decide⟩)) :
            Matrix (Fin 3) (Fin 3) (LaurentPolynomial ℤ)) = _ from BurauFaithful.burauRep3_x]
    fin_cases i <;> fin_cases j <;> simp [specM1, LaurentPolynomial.eval₂_T] <;> norm_num
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, hmat]
  decide
