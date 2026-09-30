-- Prove2me | solution 1 for BurauFaithful.burau_three_spec_twist_pow_six
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-29T15:41:28.666529+00:00
-- url     : https://prove2.me/submissions/7842fb74-f093-47ce-90e8-b7fda981ac45

/-
`BurauFaithful.burau_three_spec_twist_pow_six`:
at `t = -1` the Burau matrix of `σ₁σ₂` becomes `!![2, -2, 1; 1, 0, 0; 0, 1, 0]`, whose sixth
power is the identity (Birman, §3.3, Theorem 3.15, pp. 129--130).
-/
import Definitions.Def_BurauFaithful_UnreducedBurau
import Theorems.Thm_BurauFaithful_burauRep3_y

set_option autoImplicit false

open LaurentPolynomial Matrix BraidsLinksMCG

/-- The specialization `ℤ[t,t⁻¹] → ℤ`, `t ↦ -1`. -/
noncomputable def specM1 : (LaurentPolynomial ℤ) →+* ℤ :=
  LaurentPolynomial.eval₂ (Int.castRingHom ℤ) (-1 : ℤˣ)

theorem solution :
    (Matrix.GeneralLinearGroup.map specM1
      (BurauFaithful.burauRep 3 (BraidsLinksMCG.sigma ⟨0, by decide⟩ *
        BraidsLinksMCG.sigma ⟨1, by decide⟩))) ^ 6 = 1 := by
  have hmat : (Matrix.GeneralLinearGroup.map specM1
      (BurauFaithful.burauRep 3 (BraidsLinksMCG.sigma ⟨0, by decide⟩ *
        BraidsLinksMCG.sigma ⟨1, by decide⟩)) : Matrix (Fin 3) (Fin 3) ℤ) =
      !![ 2, -2, 1;
          1,  0, 0;
          0,  1, 0 ] := by
    ext i j
    rw [Matrix.GeneralLinearGroup.map_apply]
    rw [show (↑(BurauFaithful.burauRep 3 (BraidsLinksMCG.sigma ⟨0, by decide⟩ *
          BraidsLinksMCG.sigma ⟨1, by decide⟩)) :
            Matrix (Fin 3) (Fin 3) (LaurentPolynomial ℤ)) = _ from BurauFaithful.burauRep3_y]
    fin_cases i <;> fin_cases j <;> simp [specM1, LaurentPolynomial.eval₂_T] <;> norm_num
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, hmat]
  decide
