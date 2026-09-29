-- Prove2me | solution 1 for GaloisRepAdic.exists_charpoly_eq_scaleRoots_of_character
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/6e715eae-106b-5382-a2f3-5aac74695ffb

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_exists_charpoly_eq_scaleRoots_of_character

set_option autoImplicit false
open Polynomial

namespace GaloisRepAdic
p2m_export "GaloisRepAdic" "det finrank_eq ρ isAdicContinuous V"
namespace TW
p2m_open "GaloisRepAdic"

theorem scaleRoots_quadratic {R : Type} [CommRing R] (t d e : R) :
    (X ^ 2 - C t * X + C d).scaleRoots e = X ^ 2 - C (e * t) * X + C (e ^ 2 * d) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  have hdeg : (X ^ 2 - C t * X + C d : R[X]).natDegree = 2 := by
    have : (X ^ 2 - C t * X + C d : R[X]) = C 1 * X ^ 2 + C (-t) * X + C d := by
      simp only [map_one, one_mul, map_neg, neg_mul, sub_eq_add_neg]
    rw [this, natDegree_quadratic one_ne_zero]
  ext i
  rw [coeff_scaleRoots, hdeg]
  simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C]
  rcases i with _ | _ | _ | i
  · norm_num; ring
  · norm_num; ring
  · norm_num
  · have h1 : i + 3 ≠ 2 := by omega
    have h3 : i + 3 ≠ 0 := by omega
    simp [h1, h3]

theorem charpoly_smul_fin_two {A : Type} [CommRing A] [Nontrivial A] (e : A) (M : Matrix (Fin 2) (Fin 2) A) :
    (e • M).charpoly = M.charpoly.scaleRoots e := by
  rw [Matrix.charpoly_fin_two, Matrix.charpoly_fin_two, scaleRoots_quadratic, Matrix.trace_smul, Matrix.det_smul,
    Fintype.card_fin, smul_eq_mul]

private theorem _root_.LinearMap.charpoly_smul_of_finrank_eq_two {A V : Type} [CommRing A] [Nontrivial A]
    [AddCommGroup V] [Module A V] [Module.Free A V] [Module.Finite A V] (hV : Module.finrank A V = 2)
    (e : A) (f : Module.End A V) :
    LinearMap.charpoly (e • f) = (LinearMap.charpoly f).scaleRoots e := by
  let b := Module.finBasisOfFinrankEq A V hV
  rw [← LinearMap.charpoly_toMatrix (e • f) b, ← LinearMap.charpoly_toMatrix f b, map_smul,
    charpoly_smul_fin_two]

p2m_alias "P2MW.S_GaloisRepAdic_exists_charpoly_eq_scaleRoots_of_character.LinearMap.charpoly_smul_of_finrank_eq_two" "LinearMap.charpoly_smul_of_finrank_eq_two"

noncomputable def twist {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)
    (ε : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Aˣ)
    (hε : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) → ε σ = 1) :
    GaloisRepAdic A where
  V := ρ.V
  finrank_eq := ρ.finrank_eq
  ρ := { toFun := fun σ => ((ε σ : Aˣ) : A) • ρ.ρ σ
         map_one' := by simp only [map_one, Units.val_one, one_smul]
         map_mul' := fun σ τ => by simp only [map_mul, Units.val_mul, smul_mul_smul_comm] }
  isAdicContinuous := by
    intro n
    obtain ⟨L, hL, h1⟩ := ρ.isAdicContinuous n
    obtain ⟨L', hL', h2⟩ := hε
    haveI := hL; haveI := hL'
    refine ⟨L ⊔ L', IntermediateField.finiteDimensional_sup L L', fun σ hσ v => ?_⟩
    have hσL : ∀ x ∈ L, σ x = x := fun x hx => hσ x ((le_sup_left : L ≤ L ⊔ L') hx)
    have hσL' : ∀ x ∈ L', σ x = x := fun x hx => hσ x ((le_sup_right : L' ≤ L ⊔ L') hx)
    show ((ε σ : Aˣ) : A) • ρ.ρ σ v - v ∈ _
    rw [h2 σ hσL', Units.val_one, one_smul]
    exact h1 σ hσL v

theorem charpoly_twist {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)
    (ε : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Aˣ)
    (hε : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) → ε σ = 1)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.charpoly ((twist ρ ε hε).ρ σ) = (LinearMap.charpoly (ρ.ρ σ)).scaleRoots ((ε σ : Aˣ) : A) :=
  LinearMap.charpoly_smul_of_finrank_eq_two ρ.finrank_eq _ _

end GaloisRepAdic.TW

theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)
    (ε : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Aˣ)
    (hε : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) → ε σ = 1) :
    ∃ ρ' : GaloisRepAdic A, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      LinearMap.charpoly (ρ'.ρ σ) = (LinearMap.charpoly (ρ.ρ σ)).scaleRoots ((ε σ : Aˣ) : A) :=
  ⟨GaloisRepAdic.TW.twist ρ ε hε, GaloisRepAdic.TW.charpoly_twist ρ ε hε⟩

end S_GaloisRepAdic_exists_charpoly_eq_scaleRoots_of_character
end P2MW
export P2MW.S_GaloisRepAdic_exists_charpoly_eq_scaleRoots_of_character (solution)
