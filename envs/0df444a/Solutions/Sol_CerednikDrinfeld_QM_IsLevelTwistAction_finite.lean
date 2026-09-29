-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsLevelTwistAction.finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/9458fe53-ea3f-508f-bd8b-114d3992a64d

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsLevelTwistAction_finite

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem solution

    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N) (hN : Squarefree N)

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (hrbarn : ¬ rbar ∣ n) (hnN : Nat.Coprime n N)
    (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)

    (hsep : IsSeparated fM) (hfin : ∀ F : Finset M, ∃ U : M.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)
    (G : Type) [Group G] (ρ : G →* Aut M) (χ : G → ↥Λ) (hρ : IsLevelTwistAction Λ N n M fM ptF G ρ χ)

    (𝒴 : HeckeTower.AwayPrime r rbar → Scheme.{0}) (g : ∀ ℓ : HeckeTower.AwayPrime r rbar, 𝒴 ℓ ⟶ Spec (CommRingCat.of 𝒪))
    (ptT : ∀ (ℓ : HeckeTower.AwayPrime r rbar) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S → SchemeHomOver s (g ℓ))
    (h𝒴 : ∀ ℓ : HeckeTower.AwayPrime r rbar, IsCoarseModuliT Λ N (ℓ.1 : ℕ) (𝒴 ℓ) (g ℓ) (ptT ℓ)) :
    Finite G := by
  classical

  haveI : Module.Finite ℤ ↥Λ := (Module.Finite.iff_fg (R := ℤ) (N := Λ)).mpr hΛ.isOrder.fg

  let K : Submodule ℤ ↥Λ := LinearMap.range ((n : ℤ) • (LinearMap.id : ↥Λ →ₗ[ℤ] ↥Λ))
  haveI : Module.Finite ℤ (↥Λ ⧸ K) := Module.Finite.quotient ℤ K
  let f : G → (↥Λ ⧸ K) := fun g => Submodule.Quotient.mk (χ g)
  have hf : Function.Injective f := by
    intro g g' h
    apply hρ.label_injective
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp ((Submodule.Quotient.eq K).mp h)
    refine ⟨y, ?_⟩
    have := congrArg Subtype.val hy
    simp only [LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_smul, Submodule.coe_sub] at this
    rw [← this, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]

  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have htors : Module.IsTorsion ℤ (↥Λ ⧸ K) := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective K x
    refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero hn0⟩, ?_⟩
    show (n : ℤ) • (K.mkQ z) = 0
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨z, rfl⟩
  haveI : Finite (↥Λ ⧸ K) := Module.finite_of_fg_torsion _ htors
  exact Finite.of_injective f hf

end S_CerednikDrinfeld_QM_IsLevelTwistAction_finite
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsLevelTwistAction_finite (solution)
