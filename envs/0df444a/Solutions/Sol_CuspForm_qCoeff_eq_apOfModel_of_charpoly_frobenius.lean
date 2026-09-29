-- Prove2me | solution 1 for CuspForm.qCoeff_eq_apOfModel_of_charpoly_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/48a9b958-c6a8-528a-b185-e277e0be6e5c

import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_qCoeff_eq_apOfModel_of_charpoly_frobenius

set_option autoImplicit false
open Polynomial

namespace GlueAux4S8

lemma left_eq_of_quadratic_eq {R : Type} [CommRing R] {a b c : R}
    (h : X ^ 2 - C a * X + C c = X ^ 2 - C b * X + C c) : a = b := by
  have h1 := congrArg (fun p : R[X] => p.coeff 1) h
  simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X_one, coeff_C, mul_one,
    if_neg (show (1 : ℕ) ≠ 2 by decide), if_neg (show (1 : ℕ) ≠ 0 by decide),
    zero_sub, add_zero] at h1
  exact neg_injective h1

end GlueAux4S8

theorem solution
    {M : ℕ} [NeZero M] (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (S : Finset ℕ)
    (chig : CuspForm.heckeAlgebra M 2 (↑S : Set ℕ) →+* ℂ)
    (hchig : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      chig (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) = ModularFormClass.qCoeff g ℓ)
    (O' : Type) [CommRing O'] [IsLocalRing O'] [CharZero O']
    (iota : chig.range →+* O') (hiota : Function.Injective iota)
    (W : WeierstrassCurve ℤ) (ρ : GaloisRepAdic O')
    (hρg : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρ.ρ σ) =
            X ^ 2 - C ((iota.comp chig.rangeRestrict) (CuspForm.heckeAlgebra.T hℓ hℓM hℓS)) * X
              + C ((ℓ : O')))
    (hρW : ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ℓ ∉ (↑S : Set ℕ) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρ.ρ σ) = X ^ 2 - C ((W.apOfModel ℓ : O')) * X + C ((ℓ : O'))) :
    ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ℓ ∉ (↑S : Set ℕ) →
      ModularFormClass.qCoeff g ℓ = (W.apOfModel ℓ : ℂ) := by
  intro ℓ hℓ hgood hℓM hℓS
  obtain ⟨A, hA, σ, hσ⟩ := ValuationSubring.exists_isFrobeniusAt_rat ℓ hℓ
  have h1 := hρg ℓ hℓ hℓM hℓS A hA σ hσ
  have h2 := hρW ℓ hℓ hgood hℓS A hA σ hσ
  rw [h1] at h2
  have h4 : (iota.comp chig.rangeRestrict) (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) =
      ((W.apOfModel ℓ : O')) := GlueAux4S8.left_eq_of_quadratic_eq h2
  have h5 : chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) =
      ((W.apOfModel ℓ : ℤ) : chig.range) := by
    apply hiota
    rw [map_intCast]
    exact h4
  have h6 : (chig.rangeRestrict (CuspForm.heckeAlgebra.T hℓ hℓM hℓS) : ℂ) =
      ((W.apOfModel ℓ : ℤ) : ℂ) := by
    rw [h5]
    norm_cast
  rw [← hchig ℓ hℓ hℓM hℓS]
  exact h6

end S_CuspForm_qCoeff_eq_apOfModel_of_charpoly_frobenius
end P2MW
export P2MW.S_CuspForm_qCoeff_eq_apOfModel_of_charpoly_frobenius (solution)
