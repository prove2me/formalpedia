-- Prove2me | solution 1 for CuspForm.heckeLocal.exists_algEquiv_apply_pi_T_eq_of_dvd_of_sq_dvd_of_not_cube_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/f7de1ff6-8522-55ab-a0f3-6d2d5ac20a39

import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_CohCarrier_Tower
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Nat.Factorization.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_heckeLocal_exists_algEquiv_apply_pi_T_eq_of_dvd_of_sq_dvd_of_not_cube_dvd

set_option autoImplicit false

open Polynomial IsLocalRing

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (hirr : ρbar.IsIrreducible)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hpS : p ∈ S)

    (M M' : ℕ) [NeZero M] [NeZero M'] (hMM' : M ∣ M')
    (hM'S : ∀ q : ℕ, q.Prime → q ∣ M' → q ∈ S)

    (hsat : ∀ q : ℕ, q.Prime → q ∣ M' → q ≠ p → (q ^ 2 ∣ M ∨ ∀ n : ℕ, q ^ n ∣ M' → q ^ n ∣ M))

    (hM'3 : ∀ q : ℕ, q.Prime → q ≠ p → ¬ q ^ 3 ∣ M')

    (hpM : ∀ k : ℕ, p ^ k ∣ M' → p ^ k ∣ M)

    (hram : ∀ q : ℕ, q.Prime → q ∣ M' → q ≠ p →
      ρbar.IsUnramifiedAt q ∨ (GaloisRepAdic.ofResidualGaloisRep ρbar).IsUnipotentOnInertiaAt q)
    [Fact (CuspForm.HasIntegralStructure M 2)] [Fact (CuspForm.HasIntegralStructure M' 2)]

    (θ : CuspForm.heckeAlgebra M 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (θ' : CuspForm.heckeAlgebra M' 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθθ' : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM' : ¬ ℓ ∣ M') (hℓS : ℓ ∉ (↑S : Set ℕ)),
      θ' (CuspForm.heckeAlgebra.T hℓ hℓM' hℓS) =
        θ (CuspForm.heckeAlgebra.T hℓ (fun h => hℓM' (h.trans hMM')) hℓS))
    (hθ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ (CuspForm.heckeAlgebra.T hℓ hℓM hℓS)) * X + C (ℓ : ResidueField 𝒪)) :
    ∃ e : CuspForm.heckeLocal M' (↑S : Set ℕ) 𝒪 θ' ≃ₐ[𝒪] CuspForm.heckeLocal M (↑S : Set ℕ) 𝒪 θ,
      ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM' : ¬ ℓ ∣ M') (hℓS : ℓ ∉ (↑S : Set ℕ)),
        e (CuspForm.heckeLocal.π M' (↑S : Set ℕ) 𝒪 θ' (CuspForm.heckeAlgebra.T hℓ hℓM' hℓS)) =
          CuspForm.heckeLocal.π M (↑S : Set ℕ) 𝒪 θ
            (CuspForm.heckeAlgebra.T hℓ (fun h => hℓM' (h.trans hMM')) hℓS) := by

  have hM'M : M' ∣ M := by
    refine (Nat.dvd_iff_prime_pow_dvd_dvd M M').mpr fun q k hq hqk => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    by_cases hqp : q = p
    · rw [hqp] at hqk ⊢
      exact hpM k hqk
    have hqM' : q ∣ M' := (dvd_pow_self q hk.ne').trans hqk
    rcases hsat q hq hqM' hqp with h2 | hall
    ·
      have hk2 : k ≤ 2 := by
        by_contra hk3
        exact hM'3 q hq hqp ((pow_dvd_pow q (by omega)).trans hqk)
      exact (pow_dvd_pow q hk2).trans h2
    ·
      exact hall k hqk

  obtain rfl : M = M' := Nat.dvd_antisymm hMM' hM'M

  have hθeq : θ' = θ := by
    apply RingHom.toIntAlgHom_injective
    refine AlgHom.ext_of_eq_adjoin
      (show CuspForm.heckeAlgebra M 2 (↑S : Set ℕ) =
        Algebra.adjoin ℤ (CuspForm.heckeGenerators M 2 (↑S : Set ℕ)) from rfl) ?_
    intro x hx
    rcases hx with ⟨ℓ, hℓ, hℓN, hℓS, rfl⟩ | ⟨q, hqN, hq, hqS, rfl⟩
    · exact hθθ' ℓ hℓ hℓN hℓS
    · exact (hqS (Finset.mem_coe.mpr (hM'S q hq hqN))).elim
  subst hθeq

  exact ⟨AlgEquiv.refl, fun ℓ hℓ hℓM' hℓS => rfl⟩

end S_CuspForm_heckeLocal_exists_algEquiv_apply_pi_T_eq_of_dvd_of_sq_dvd_of_not_cube_dvd
end P2MW
export P2MW.S_CuspForm_heckeLocal_exists_algEquiv_apply_pi_T_eq_of_dvd_of_sq_dvd_of_not_cube_dvd (solution)
