-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFineModuli.apply_eq_apply_of_isPullback_of_frobTwist_eq_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/62fd38d0-31c3-55f9-8695-ecc7f7d225bf

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_AlgFunctorConst
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_ClassSetGraph

import Theorems.Thm_CerednikDrinfeld_FormalOmega_existsUnique_factor_corep_fixedPoints_of_frobTwist_eq
import Theorems.Thm_CerednikDrinfeld_FormalOmega_Omega_action_scalarGL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuli_apply_eq_apply_of_isPullback_of_frobTwist_eq_of_invariant

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega NeronModelInfra

namespace IUAux

theorem zpow_apply_eq_self {R A : Type} [CommSemiring R] [Semiring A] [Algebra R A] (σ : A ≃ₐ[R] A) (w : A)
    (h : σ w = w) (k : ℤ) : (σ ^ k) w = w := by
  have hn : ∀ n : ℕ, (σ ^ n) w = w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, AlgEquiv.mul_apply, h, ih]
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [zpow_natCast]; exact hn n
  · rw [zpow_neg, zpow_natCast]
    have e := hn n
    calc (σ ^ n)⁻¹ w = (σ ^ n)⁻¹ ((σ ^ n) w) := by rw [e]
      _ = ((σ ^ n)⁻¹ * σ ^ n) w := (AlgEquiv.mul_apply _ _ _).symm
      _ = w := by rw [inv_mul_cancel, AlgEquiv.one_apply]

end IUAux

theorem solution

    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N)

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪ˣ, (Matrix.GeneralLinearGroup.det g : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n)

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of 𝒪))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)), FakeEllipticCurve Λ N S → SchemeHomOver s f)
    (h𝒳 : IsCoarseModuli Λ N 𝒳 f pt)

    (n : ℕ) (hn : 3 ≤ n) (hrn : ¬ r ∣ n) (hrbarn : ¬ rbar ∣ n) (hnN : Nat.Coprime n N)
    (M : Scheme.{0}) (fM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N n S → SchemeHomOver s fM)
    (hM : IsFineModuli Λ N n M fM ptF)
    (G : Type) [Group G] (ρ : G →* Aut M) (χ : G → ↥Λ) (hρ : IsLevelTwistAction Λ N n M fM ptF G ρ χ)

    (p : M ⟶ 𝒳) (hp : p ≫ f = fM) (hρp : ∀ h : G, (ρ h).hom ≫ p = p)
    (hp_pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithFullLevel Λ N n S),
      (ptF S s u).1 ≫ p = (pt S s u.1).1)
    (𝒴 : HeckeTower.AwayPrime r rbar → Scheme.{0}) (g : ∀ ℓ : HeckeTower.AwayPrime r rbar, 𝒴 ℓ ⟶ Spec (CommRingCat.of 𝒪))
    (ptT : ∀ (ℓ : HeckeTower.AwayPrime r rbar) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S → SchemeHomOver s (g ℓ))
    (h𝒴 : ∀ ℓ : HeckeTower.AwayPrime r rbar, IsCoarseModuliT Λ N (ℓ.1 : ℕ) (𝒴 ℓ) (g ℓ) (ptT ℓ))
    (d₀ d₁ : ∀ ℓ : HeckeTower.AwayPrime r rbar, 𝒴 ℓ ⟶ 𝒳) (hd₀f : ∀ ℓ, d₀ ℓ ≫ f = g ℓ) (hd₁f : ∀ ℓ, d₁ ℓ ≫ f = g ℓ)
    (hd₀ : ∀ (ℓ : HeckeTower.AwayPrime r rbar) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S), (ptT ℓ S s u).1 ≫ d₀ ℓ = (pt S s u.1).1)
    (hd₁ : ∀ (ℓ : HeckeTower.AwayPrime r rbar) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
      (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) S) (d : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsLevelIsogeny (ℓ.1 : ℕ) u d → (ptT ℓ S s u).1 ≫ d₁ ℓ = (pt S s d).1)

    (ar arbar : 𝒳 ⟶ 𝒳) (harf : ar ≫ f = f) (harbarf : arbar ≫ f = f)
    (har : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsAtkinLehnerQuotient r E E' → (pt S s E).1 ≫ ar = (pt S s E').1)
    (harbar : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (E E' : FakeEllipticCurve Λ N S),
      FakeEllipticCurve.IsAtkinLehnerQuotient rbar E E' → (pt S s E).1 ≫ arbar = (pt S s E').1)

    {a₁ b₁ : ℚ} (hdef : IsDefiniteRamifiedExactlyAt (a := a₁) (b := b₁) rbar)
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (n₁ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₁ : n₁ ∈ primeHeckeSet R₁ r)
    (hS₁ : IsEichlerOrder (meetOrder R₁ n₁) (N * r))
    (ι₀ : ℍ[ℚ, a₁, b₁] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) K₀) (hι₀ : Function.Injective ι₀)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)

    (Γt : Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (hΓt : ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γt ↔ x ∈ CerednikDrinfeld.CosetGraph.awayUnits R₁ v)
    (s : HeckeTower.AwayPrime r rbar → (ℍ[ℚ, a₁, b₁])ˣ)
    (sf : HeckeTower.AwayPrime r rbar → (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs : ∀ ℓ : HeckeTower.AwayPrime r rbar,
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s ℓ : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf ℓ : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * (sf ℓ)⁻¹ ∈
        (if (ℓ.1 : ℕ) ∣ N then levelHeckeUSet Λ₁ (meetOrder R₁ n₁) (ℓ.1 : ℕ)
          else primeHeckeSet (meetOrder R₁ n₁) (ℓ.1 : ℕ)) ∧
      nrd (s ℓ : ℍ[ℚ, a₁, b₁]) = ((ℓ.1 : ℕ) : ℚ))
    (Γtℓ : HeckeTower.AwayPrime r rbar → Subgroup (ℍ[ℚ, a₁, b₁])ˣ) (hΓtℓ : ∀ ℓ : HeckeTower.AwayPrime r rbar, Γtℓ ℓ = Γt ⊓ Γt.map (MulAut.conj (s ℓ)).toMonoidHom)

    (wbar : (ℍ[ℚ, a₁, b₁])ˣ) (hwbar : nrd (wbar : ℍ[ℚ, a₁, b₁]) = ((rbar : ℕ) : ℚ) ∧ ∀ x : (ℍ[ℚ, a₁, b₁])ˣ, x ∈ Γt → wbar * x * wbar⁻¹ ∈ Γt)

    (θt : ↥Γt →* G)
    (Θf : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B → (Scheme.nilpPoints fM).obj B)

    (hnat :
      ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
          Θf B' hB' ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map φ x) = (Scheme.nilpPoints fM).map φ (Θf B hB x))

    (hG :
      ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B) (g h : G),
          (Scheme.nilpPoints.mapHom fM fM (ρ h).hom (hρ.over_base h)).app B (Θf B hB (x, g * h)) = Θf B hB (x, g))

    (hinv :
      ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : (ℍ[ℚ, a₁, b₁])ˣ) (hγ : γ ∈ Γt)
          (x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B) (g : G),
          OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ) x x' → Θf B hB (x', θt ⟨γ, hγ⟩ * g) = Θf B hB (x, g))

    (het :
      ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B₀ : Type) [CommRing B₀] [Algebra 𝒪 B₀] (p : B →ₐ[𝒪] B₀)
          (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB₀ : IsNilpotent (algebraMap 𝒪 B₀ π)),
          Function.Surjective p → (∀ s t : B, p s = 0 → p t = 0 → s * t = 0) →
          ∀ (x₀ : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B₀) (y : (Scheme.nilpPoints fM).obj B), (Scheme.nilpPoints fM).map p y = Θf B₀ hB₀ x₀ →
            ∃! x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B, (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map p x = x₀ ∧ Θf B hB x = y)

    (hgeom :
      ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π)) (ψ : Onr →ₐ[𝒪] k),
          (∀ y : (Scheme.nilpPoints fM).obj k, ∃ (P : (Omega K₀ π).obj k) (g : G), Θf k hk ((ψ, P), g) = y) ∧
          ∀ (ψ' : Onr →ₐ[𝒪] k) (P P' : (Omega K₀ π).obj k) (g g' : G),
            Θf k hk ((ψ, P), g) = Θf k hk ((ψ', P'), g') ↔
              ∃ (γ : (ℍ[ℚ, a₁, b₁])ˣ) (hγ : γ ∈ Γt), g' = θt ⟨γ, hγ⟩ * g ∧
                DeligneDatum.IsPullback (K := K₀) (π := π) k ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ)⁻¹ P P' ∧
                ∀ y : Onr, (∀ (z : (ℍ[ℚ, a₁, b₁])ˣ) (hz : z ∈ Γt), (∃ c : ℚ, (z : ℍ[ℚ, a₁, b₁]) = c • (1 : ℍ[ℚ, a₁, b₁])) →
                    θt ⟨z, hz⟩ = 1 → (Fr ^ Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z))) y = y) →
                  ψ' y = frobTwist Onr Fr (- Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ))) ψ y)

    (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
    (ρ' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B → (Scheme.nilpPoints t).obj B)
    (hρnat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
      ρ' B' hB' ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map φ x) = (Scheme.nilpPoints t).map φ (ρ' B hB x))
    (hρinv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : (ℍ[ℚ, a₁, b₁])ˣ) (hγ : γ ∈ Γt)
      (x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B) (g : G),
      OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ) x x' → ρ' B hB (x', θt ⟨γ, hγ⟩ * g) = ρ' B hB (x, g))
    :
    ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π))
      (x₁ x₂ : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj C) (γ : (ℍ[ℚ, a₁, b₁])ˣ) (hγ : γ ∈ Γt),
      DeligneDatum.IsPullback (K := K₀) (π := π) C ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ)⁻¹ x₁.1.2 x₂.1.2 →
      (∀ y : Onr, (∀ (z : (ℍ[ℚ, a₁, b₁])ˣ) (hz : z ∈ Γt), (∃ c : ℚ, (z : ℍ[ℚ, a₁, b₁]) = c • (1 : ℍ[ℚ, a₁, b₁])) →
          θt ⟨z, hz⟩ = 1 → (Fr ^ Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z))) y = y) →
        (show Onr →ₐ[𝒪] C from x₂.1.1) y =
          frobTwist Onr Fr (- Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ))) (show Onr →ₐ[𝒪] C from x₁.1.1) y) →
      @Eq G x₂.2 (@HMul.hMul G G G _ (θt ⟨γ, hγ⟩) x₁.2) →
      ρ' C hC x₂ = ρ' C hC x₁ := by
  intro C _ _ hC x₁ x₂ γ hγ hPB hψ hg
  classical

  have ft_apply : ∀ (n : ℤ) (B : Type) [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) (y : Onr),
      frobTwist Onr Fr n ψ y = ψ ((Fr ^ n) y) := fun n B _ _ ψ y => rfl
  have ft_add : ∀ (m n : ℤ) (B : Type) [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B),
      frobTwist Onr Fr m (frobTwist Onr Fr n ψ) = frobTwist Onr Fr (n + m) ψ := by
    intro m n B _ _ ψ
    apply AlgHom.ext; intro y
    rw [ft_apply, ft_apply, ft_apply, zpow_add, AlgEquiv.mul_apply]
  have ft_zero : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B), frobTwist Onr Fr 0 ψ = ψ := by
    intro B _ _ ψ
    apply AlgHom.ext; intro y
    rw [ft_apply, zpow_zero, AlgEquiv.one_apply]

  have hrefl : ∀ (z : (ℍ[ℚ, a₁, b₁])ˣ), (∃ c : ℚ, (z : ℍ[ℚ, a₁, b₁]) = c • (1 : ℍ[ℚ, a₁, b₁])) →
      ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (P : (Omega K₀ π).obj B),
        DeligneDatum.IsPullback (K := K₀) (π := π) B ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z)⁻¹ P P := by
    intro z hz B _ _ P
    obtain ⟨c, hc⟩ := hz
    have hc0 : algebraMap ℚ K₀ c ≠ 0 := by
      intro h0
      have hc' : c = 0 := by simpa using h0
      apply z.ne_zero
      rw [hc, hc', zero_smul]
    have hU : (Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z = LT.LatticeTree.scalarGL (Units.mk0 (algebraMap ℚ K₀ c) hc0) := by
      apply Units.ext
      show ι₀ (z : ℍ[ℚ, a₁, b₁]) = algebraMap ℚ K₀ c • (1 : Matrix (Fin 2) (Fin 2) K₀)
      rw [hc, map_smul, map_one, algebraMap_smul]
    rw [hU]
    have h := DeligneDatum.isPullback_pullback (K := K₀) (π := π) (B := B)
      (LT.LatticeTree.scalarGL (Units.mk0 (algebraMap ℚ K₀ c) hc0))⁻¹ P
    have hact : DeligneDatum.pullback π B (LT.LatticeTree.scalarGL (Units.mk0 (algebraMap ℚ K₀ c) hc0))⁻¹ P =
        (Omega.action K₀ π).act B (LT.LatticeTree.scalarGL (Units.mk0 (algebraMap ℚ K₀ c) hc0)) P := rfl
    rw [hact, Omega.action_scalarGL] at h
    exact h

  let v : ℤ := Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ))
  let xm : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj C := (frobTwist Onr Fr (-v) (show Onr →ₐ[𝒪] C from x₁.1.1), x₂.1.2)
  have htw : OmegaNr.IsTwistedAct π Onr Fr vdet C ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ) x₁.1 xm := ⟨rfl, hPB⟩
  have h1 : ρ' C hC (xm, θt ⟨γ, hγ⟩ * (show G from x₁.2)) = ρ' C hC (x₁.1, x₁.2) := hρinv C hC γ hγ x₁.1 xm x₁.2 htw

  let ρY : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.corep Onr) (AlgFunctor.prod (Omega K₀ π) (AlgFunctor.const G))).obj B → (Scheme.nilpPoints t).obj B :=
    fun B _ _ hB p => ρ' B hB ((p.1, p.2.1), p.2.2)
  have hρY_nat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
      (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B')
      (p : (AlgFunctor.prod (AlgFunctor.corep Onr) (AlgFunctor.prod (Omega K₀ π) (AlgFunctor.const G))).obj B),
      ρY B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (AlgFunctor.prod (Omega K₀ π) (AlgFunctor.const G))).map φ p) = (Scheme.nilpPoints t).map φ (ρY B hB p) :=
    fun B _ _ B' _ _ hB hB' φ p => hρnat B B' hB hB' φ ((p.1, p.2.1), p.2.2)

  let Ginv : AddSubgroup ℤ :=
    { carrier := {n | ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B)
        (y : (AlgFunctor.prod (Omega K₀ π) (AlgFunctor.const G)).obj B), ρY B hB (frobTwist Onr Fr n ψ, y) = ρY B hB (ψ, y)}
      zero_mem' := by
        intro B _ _ hB ψ y
        rw [ft_zero]
      add_mem' := by
        intro a b ha hb B _ _ hB ψ y
        rw [← ft_add, hb B hB (frobTwist Onr Fr a ψ) y, ha B hB ψ y]
      neg_mem' := by
        intro a ha B _ _ hB ψ y
        have := ha B hB (frobTwist Onr Fr (-a) ψ) y
        rw [ft_add, neg_add_cancel, ft_zero] at this
        exact this.symm }
  have hmemG : ∀ (n : ℤ), n ∈ Ginv ↔ ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B)
        (y : (AlgFunctor.prod (Omega K₀ π) (AlgFunctor.const G)).obj B), ρY B hB (frobTwist Onr Fr n ψ, y) = ρY B hB (ψ, y) := fun n => Iff.rfl

  have hcentral : ∀ (z : (ℍ[ℚ, a₁, b₁])ˣ) (hz : z ∈ Γt), (∃ c : ℚ, (z : ℍ[ℚ, a₁, b₁]) = c • (1 : ℍ[ℚ, a₁, b₁])) →
      θt ⟨z, hz⟩ = 1 → Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z)) ∈ Ginv := by
    intro z hz hcz hθ
    have hneg : -Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z)) ∈ Ginv := by
      rw [hmemG]
      intro B _ _ hB ψ y
      have htwz : OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z) (ψ, y.1)
          (frobTwist Onr Fr (-Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z))) ψ, y.1) := ⟨rfl, hrefl z hcz B y.1⟩
      have := hρinv B hB z hz (ψ, y.1) (frobTwist Onr Fr (-Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z))) ψ, y.1) y.2 htwz
      rw [hθ, one_mul] at this
      exact this
    have := Ginv.neg_mem hneg
    rwa [neg_neg] at this

  obtain ⟨a, ha⟩ := Int.subgroup_cyclic Ginv
  have ha_mem : a ∈ Ginv := by rw [ha]; exact AddSubgroup.mem_closure_singleton.mpr ⟨1, one_zsmul a⟩
  have hdiv : ∀ (z : (ℍ[ℚ, a₁, b₁])ˣ) (hz : z ∈ Γt), (∃ c : ℚ, (z : ℍ[ℚ, a₁, b₁]) = c • (1 : ℍ[ℚ, a₁, b₁])) →
      θt ⟨z, hz⟩ = 1 → ∃ kz : ℤ, kz • a = Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z)) := by
    intro z hz hcz hθ
    have := hcentral z hz hcz hθ
    rw [ha] at this
    exact AddSubgroup.mem_closure_singleton.mp this

  have hrepl : ρ' C hC ((x₂.1.1, x₂.1.2), x₂.2) = ρ' C hC ((xm.1, x₂.1.2), x₂.2) := by
    by_cases ha0 : a = 0
    ·
      have hall : (show Onr →ₐ[𝒪] C from x₂.1.1) = xm.1 := by
        apply AlgHom.ext; intro y
        apply hψ y
        intro z hz hcz hθ
        obtain ⟨kz, hkz⟩ := hdiv z hz hcz hθ
        rw [← hkz, ha0, smul_zero, zpow_zero, AlgEquiv.one_apply]
      exact congrArg (fun ψ => ρ' C hC ((ψ, x₂.1.2), x₂.2)) hall
    ·
      set m : ℕ := a.natAbs with hmdef
      have hm : 0 < m := Int.natAbs_pos.mpr ha0
      have hma : (m : ℤ) = a ∨ (m : ℤ) = -a := by rw [hmdef, Int.natCast_natAbs]; exact abs_choice a
      have hm_mem : (m : ℤ) ∈ Ginv := by
        rcases hma with h | h
        · rw [h]; exact ha_mem
        · rw [h]; exact Ginv.neg_mem ha_mem
      have hρY_inv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (ψ : Onr →ₐ[𝒪] B)
          (y : (AlgFunctor.prod (Omega K₀ π) (AlgFunctor.const G)).obj B), ρY B hB (frobTwist Onr Fr (m : ℤ) ψ, y) = ρY B hB (ψ, y) := (hmemG m).mp hm_mem
      obtain ⟨ρbar, -, hfac, -⟩ := CerednikDrinfeld.FormalOmega.existsUnique_factor_corep_fixedPoints_of_frobTwist_eq 𝒪 hdvr π hπ hcomplete hres hunr Onr Fr hOnr_complete hOnr_max
        hOnr_alg hOnr_closed hFr m hm (AlgFunctor.prod (Omega K₀ π) (AlgFunctor.const G)) T t ρY hρY_nat hρY_inv

      have hFa : ∀ w : Onr, (Fr ^ (m : ℤ)) w = w → (Fr ^ a) w = w := by
        intro w hw
        rcases hma with h | h
        · rw [← h]; exact hw
        · have e : (Fr ^ a) ((Fr ^ (m : ℤ)) w) = (Fr ^ a) w := by rw [hw]
          rw [← AlgEquiv.mul_apply, ← zpow_add, h, add_neg_cancel, zpow_zero, AlgEquiv.one_apply] at e
          exact e.symm
      have hcomp : (show Onr →ₐ[𝒪] C from x₂.1.1).comp
            (AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val =
          (xm.1).comp (AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val := by
        apply AlgHom.ext
        rintro ⟨w, hw⟩
        rw [AlgHom.mem_equalizer] at hw
        show (show Onr →ₐ[𝒪] C from x₂.1.1) w = (show Onr →ₐ[𝒪] C from xm.1) w
        apply hψ w
        intro z hz hcz hθ
        obtain ⟨kz, hkz⟩ := hdiv z hz hcz hθ
        rw [← hkz, smul_eq_mul, mul_comm, zpow_mul]
        exact IUAux.zpow_apply_eq_self (Fr ^ a) w (hFa w hw) kz
      have e2 := hfac C hC (show Onr →ₐ[𝒪] C from x₂.1.1) (x₂.1.2, x₂.2)
      have em := hfac C hC xm.1 (x₂.1.2, x₂.2)
      show ρY C hC (x₂.1.1, (x₂.1.2, x₂.2)) = ρY C hC (xm.1, (x₂.1.2, x₂.2))
      rw [e2, em, hcomp]

  calc ρ' C hC x₂ = ρ' C hC ((x₂.1.1, x₂.1.2), x₂.2) := rfl
    _ = ρ' C hC ((xm.1, x₂.1.2), x₂.2) := hrepl
    _ = ρ' C hC (xm, θt ⟨γ, hγ⟩ * (show G from x₁.2)) := by rw [← hg]
    _ = ρ' C hC (x₁.1, x₁.2) := h1
    _ = ρ' C hC x₁ := rfl

end S_CerednikDrinfeld_QM_IsFineModuli_apply_eq_apply_of_isPullback_of_frobTwist_eq_of_invariant
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFineModuli_apply_eq_apply_of_isPullback_of_frobTwist_eq_of_invariant (solution)
