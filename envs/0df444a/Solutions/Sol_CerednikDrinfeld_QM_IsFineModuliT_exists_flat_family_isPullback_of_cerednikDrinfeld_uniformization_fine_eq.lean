-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFineModuliT.exists_flat_family_isPullback_of_cerednikDrinfeld_uniformization_fine_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/d64e7b16-1155-501a-a1c9-74234e13bae2

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_AlgFunctorConst
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Theorems.Thm_CerednikDrinfeld_FormalOmega_Omega_map_injective_of_injective
import Theorems.Thm_CerednikDrinfeld_QM_IsFineModuliT_exists_apply_ne_zero_forall_isPullback_of_cerednikDrinfeld_uniformization_fine_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuliT_exists_flat_family_isPullback_of_cerednikDrinfeld_uniformization_fine_eq

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega NeronModelInfra

namespace Q2PointAuxT

open CerednikDrinfeld.FormalOmega

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)

theorem isPullback_iff_eq_pullback (B : Type) [CommRing B] [Algebra 𝒪 B] (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (d d' : DeligneDatum (K := K) π B) :
    DeligneDatum.IsPullback (K := K) (π := π) B g d d' ↔ d' = DeligneDatum.pullback π B g d := by
  constructor
  · intro h
    apply DeligneDatum.ext'
    funext M
    exact h M
  · rintro rfl
    exact DeligneDatum.isPullback_pullback π B g d

theorem isPullback_of_map {B B' : Type} [CommRing B] [Algebra 𝒪 B] [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
    (hf : Function.Injective ((Omega K π).map f))
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (d d' : (Omega K π).obj B)
    (h : DeligneDatum.IsPullback (K := K) (π := π) B' g ((Omega K π).map f d) ((Omega K π).map f d')) :
    DeligneDatum.IsPullback (K := K) (π := π) B g d d' := by
  rw [isPullback_iff_eq_pullback] at h ⊢
  apply hf
  change d'.map π f = (DeligneDatum.pullback π B g d).map π f
  rw [DeligneDatum.map_pullback]
  exact h

end Q2PointAuxT

open Q2PointAuxT in
theorem solution

    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N) (hN : Squarefree N)

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

    [hgr : GeometricallyReduced (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 K₀))))]
    [hgc : GeometricallyConnected (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 K₀))))]

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
      (ΘT : ∀ ℓ : HeckeTower.AwayPrime r rbar, ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints (g ℓ)).obj B)

    (hnat :
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
          Θf B' hB' ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map φ x) = (Scheme.nilpPoints fM).map φ (Θf B hB x)))

    (hG :
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B) (g h : G),
          (Scheme.nilpPoints.mapHom fM fM (ρ h).hom (hρ.over_base h)).app B (Θf B hB (x, g * h)) = Θf B hB (x, g)))

    (hinv :
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : (ℍ[ℚ, a₁, b₁])ˣ) (hγ : γ ∈ Γt)
          (x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B) (g : G),
          OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ) x x' → Θf B hB (x', θt ⟨γ, hγ⟩ * g) = Θf B hB (x, g)))

    (het :
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B₀ : Type) [CommRing B₀] [Algebra 𝒪 B₀] (p : B →ₐ[𝒪] B₀)
          (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB₀ : IsNilpotent (algebraMap 𝒪 B₀ π)),
          Function.Surjective p → (∀ s t : B, p s = 0 → p t = 0 → s * t = 0) →
          ∀ (x₀ : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B₀) (y : (Scheme.nilpPoints fM).obj B), (Scheme.nilpPoints fM).map p y = Θf B₀ hB₀ x₀ →
            ∃! x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B, (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map p x = x₀ ∧ Θf B hB x = y))
    (ℓ : HeckeTower.AwayPrime r rbar)
    (Mℓ : Scheme.{0}) (fMℓ : Mℓ ⟶ Spec (CommRingCat.of 𝒪))

    (Θfℓ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B → (Scheme.nilpPoints fMℓ).obj B)

    (hnatℓ :
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
        (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
        Θfℓ B' hB' ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map φ x) = (Scheme.nilpPoints fMℓ).map φ (Θfℓ B hB x)))

    (hinvℓ :
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : (ℍ[ℚ, a₁, b₁])ˣ) (hγ : γ ∈ Γt) (hγℓ : γ ∈ Γtℓ ℓ)
        (x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B) (g : G),
        OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ) x x' → Θfℓ B hB (x', θt ⟨γ, hγ⟩ * g) = Θfℓ B hB (x, g)))

    (hetℓ :
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B₀ : Type) [CommRing B₀] [Algebra 𝒪 B₀] (p : B →ₐ[𝒪] B₀)
        (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB₀ : IsNilpotent (algebraMap 𝒪 B₀ π)),
        Function.Surjective p → (∀ s t : B, p s = 0 → p t = 0 → s * t = 0) →
        ∀ (x₀ : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B₀) (y : (Scheme.nilpPoints fMℓ).obj B), (Scheme.nilpPoints fMℓ).map p y = Θfℓ B₀ hB₀ x₀ →
          ∃! x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B, (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map p x = x₀ ∧ Θfℓ B hB x = y))

    (hfibℓ :
    (∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π)) (ψ : Onr →ₐ[𝒪] k),
        ∀ (ψ' : Onr →ₐ[𝒪] k) (P P' : (Omega K₀ π).obj k) (g g' : G),
          Θfℓ k hk ((ψ, P), g) = Θfℓ k hk ((ψ', P'), g') ↔
            ∃ (γ : (ℍ[ℚ, a₁, b₁])ˣ) (hγ : γ ∈ Γt), γ ∈ Γtℓ ℓ ∧ g' = θt ⟨γ, hγ⟩ * g ∧
              DeligneDatum.IsPullback (K := K₀) (π := π) k ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ)⁻¹ P P' ∧
              ∀ y : Onr, (∀ (z : (ℍ[ℚ, a₁, b₁])ˣ) (hz : z ∈ Γt), (∃ c : ℚ, (z : ℍ[ℚ, a₁, b₁]) = c • (1 : ℍ[ℚ, a₁, b₁])) →
                  θt ⟨z, hz⟩ = 1 → (Fr ^ Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z))) y = y) →
                ψ' y = frobTwist Onr Fr (- Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ))) ψ y))

    (hfMℓ : LocallyOfFiniteType fMℓ)
    :

    ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (x₁ x₂ : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B) (g₁ g₂ : G),
      Θfℓ B hB (x₁, g₁) = Θfℓ B hB (x₂, g₂) →
      ∃ (k : ℕ) (B' : Fin k → Type) (_ : ∀ i, CommRing (B' i)) (_ : ∀ i, Algebra 𝒪 (B' i)) (_ : ∀ i, Algebra B (B' i))
        (_ : ∀ i, IsScalarTower 𝒪 B (B' i)) (_ : ∀ i, Module.Flat B (B' i))
        (hcov : ∀ 𝔭 : PrimeSpectrum B, ∃ (i : Fin k) (𝔮 : PrimeSpectrum (B' i)), 𝔮.comap (algebraMap B (B' i)) = 𝔭)
        (γ : Fin k → (ℍ[ℚ, a₁, b₁])ˣ) (hγ : ∀ i, γ i ∈ Γt) (hγℓ : ∀ i, γ i ∈ Γtℓ ℓ),
        ∀ i,
          DeligneDatum.IsPullback (K := K₀) (π := π) (B' i) ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) (γ i))⁻¹ ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (IsScalarTower.toAlgHom 𝒪 B (B' i)) x₁).2 ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (IsScalarTower.toAlgHom 𝒪 B (B' i)) x₂).2 ∧
          (∀ y : Onr, (∀ (z : (ℍ[ℚ, a₁, b₁])ˣ) (hz : z ∈ Γt), (∃ c : ℚ, (z : ℍ[ℚ, a₁, b₁]) = c • (1 : ℍ[ℚ, a₁, b₁])) →
              θt ⟨z, hz⟩ = 1 → (Fr ^ Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z))) y = y) →
            (show Onr →ₐ[𝒪] B' i from ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (IsScalarTower.toAlgHom 𝒪 B (B' i)) x₂).1) y =
              frobTwist Onr Fr (- Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) (γ i)))) (show Onr →ₐ[𝒪] B' i from ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map (IsScalarTower.toAlgHom 𝒪 B (B' i)) x₁).1) y) ∧
          g₂ = θt ⟨γ i, hγ i⟩ * g₁ := by
  intro B _ _ hBπ x₁ x₂ g₁ g₂ h
  classical

  have HP : ∀ (L : Type) [Field L] [Algebra 𝒪 L] (φ : B →ₐ[𝒪] L),
      ∃ (γ : (ℍ[ℚ, a₁, b₁])ˣ) (hγ : γ ∈ Γt), γ ∈ Γtℓ ℓ ∧
        (DeligneDatum.IsPullback (K := K₀) (π := π) L ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ)⁻¹ ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x₁).2 ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x₂).2 ∧
          (∀ y : Onr, (∀ (z : (ℍ[ℚ, a₁, b₁])ˣ) (hz : z ∈ Γt), (∃ c : ℚ, (z : ℍ[ℚ, a₁, b₁]) = c • (1 : ℍ[ℚ, a₁, b₁])) →
              θt ⟨z, hz⟩ = 1 → (Fr ^ Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z))) y = y) →
            (show Onr →ₐ[𝒪] L from ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x₂).1) y =
              frobTwist Onr Fr (- Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ))) (show Onr →ₐ[𝒪] L from ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x₁).1) y) ∧
          g₂ = θt ⟨γ, hγ⟩ * g₁) := by
    intro L _ _ φ

    let k : Type := AlgebraicClosure L
    let ι : L →ₐ[𝒪] k := IsScalarTower.toAlgHom 𝒪 L k
    have hι : Function.Injective ι := (algebraMap L k).injective
    let ρ' : B →ₐ[𝒪] k := ι.comp φ
    have hk : IsNilpotent (algebraMap 𝒪 k π) := by
      obtain ⟨n, hn⟩ := hBπ
      refine ⟨n, ?_⟩
      rw [← ρ'.commutes, ← map_pow, hn, map_zero]

    have heq : Θfℓ k hk ((ρ'.comp x₁.1, (Omega K₀ π).map ρ' x₁.2), g₁) = Θfℓ k hk ((ρ'.comp x₂.1, (Omega K₀ π).map ρ' x₂.2), g₂) := by
      have h₁ := hnatℓ B k hBπ hk ρ' (x₁, g₁)
      have h₂ := hnatℓ B k hBπ hk ρ' (x₂, g₂)
      rw [h] at h₁
      exact h₁.trans h₂.symm
    obtain ⟨γ, hγ, hγℓ, hg, hP, hψ⟩ :=
      (hfibℓ k hk (ρ'.comp x₁.1) (ρ'.comp x₂.1) ((Omega K₀ π).map ρ' x₁.2) ((Omega K₀ π).map ρ' x₂.2) g₁ g₂).mp heq
    refine ⟨γ, hγ, hγℓ, ?_, ?_, hg⟩
    ·
      apply isPullback_of_map π ι
        (CerednikDrinfeld.FormalOmega.Omega.map_injective_of_injective (K := K₀) π ι hι)
      have c₁ : (Omega K₀ π).map ι ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x₁).2 =
          (Omega K₀ π).map ρ' x₁.2 := ((Omega K₀ π).map_comp φ ι x₁.2).symm
      have c₂ : (Omega K₀ π).map ι ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x₂).2 =
          (Omega K₀ π).map ρ' x₂.2 := ((Omega K₀ π).map_comp φ ι x₂.2).symm
      rw [c₁, c₂]
      exact hP
    ·
      intro y hy
      apply hι
      exact hψ y hy

  have HS := CerednikDrinfeld.QM.IsFineModuliT.exists_apply_ne_zero_forall_isPullback_of_cerednikDrinfeld_uniformization_fine_eq
    hrr hrN hrbarN hN 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet hB Λ hΛ 𝒳 f pt h𝒳 n hn hrn hrbarn hnN M fM ptF hM G ρ χ hρ p hp hρp hp_pt 𝒴 g ptT h𝒴 d₀ d₁ hd₀f hd₁f hd₀ hd₁ ar arbar harf harbarf har harbar hdef Λ₁ R₁ hΛ₁ hR₁ hRΛ₁ n₁ hn₁ hS₁ ι₀ hι₀ v hv Γt hΓt s sf hs Γtℓ hΓtℓ wbar hwbar θt Θf ΘT hnat hG hinv het ℓ Mℓ fMℓ Θfℓ hnatℓ hinvℓ hetℓ hfMℓ B hBπ x₁ x₂ g₁ g₂ h

  have key : ∀ 𝔭 : PrimeSpectrum B, ∃ (f : B) (γ : (ℍ[ℚ, a₁, b₁])ˣ) (hγ : γ ∈ Γt), γ ∈ Γtℓ ℓ ∧ f ∉ 𝔭.asIdeal ∧
      ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] (χ : B →ₐ[𝒪] C), IsUnit (χ f) →
        DeligneDatum.IsPullback (K := K₀) (π := π) C ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ)⁻¹ ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map χ x₁).2 ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map χ x₂).2 ∧
        (∀ y : Onr, (∀ (z : (ℍ[ℚ, a₁, b₁])ˣ) (hz : z ∈ Γt), (∃ c : ℚ, (z : ℍ[ℚ, a₁, b₁]) = c • (1 : ℍ[ℚ, a₁, b₁])) →
              θt ⟨z, hz⟩ = 1 → (Fr ^ Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) z))) y = y) →
          (show Onr →ₐ[𝒪] C from ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map χ x₂).1) y =
            frobTwist Onr Fr (- Multiplicative.toAdd (vdet ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ))) (show Onr →ₐ[𝒪] C from ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map χ x₁).1) y) ∧
        g₂ = θt ⟨γ, hγ⟩ * g₁ := by
    intro 𝔭
    let L : Type := 𝔭.asIdeal.ResidueField
    letI : Algebra 𝒪 L := ((algebraMap B L).comp (algebraMap 𝒪 B)).toAlgebra
    haveI : IsScalarTower 𝒪 B L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    let φ : B →ₐ[𝒪] L := IsScalarTower.toAlgHom 𝒪 B L
    obtain ⟨γ, hγ, hγℓ, hrel⟩ := HP L φ
    obtain ⟨f, hf, H⟩ := HS L φ γ hγ hγℓ hrel
    refine ⟨f, γ, hγ, hγℓ, ?_, H⟩
    intro hmem
    exact hf (Ideal.algebraMap_residueField_eq_zero.mpr hmem)
  choose f γ hγ hγℓ hf H using key

  have hcover : (Set.univ : Set (PrimeSpectrum B)) ⊆ ⋃ 𝔭 : PrimeSpectrum B, (PrimeSpectrum.basicOpen (f 𝔭) : Set (PrimeSpectrum B)) :=
    fun 𝔭 _ => Set.mem_iUnion.mpr ⟨𝔭, hf 𝔭⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun 𝔭 : PrimeSpectrum B => (PrimeSpectrum.basicOpen (f 𝔭) : Set (PrimeSpectrum B)))
    (fun 𝔭 => (PrimeSpectrum.basicOpen (f 𝔭)).isOpen) hcover

  let e : Fin t.card ≃ ↥t := t.equivFin.symm
  let 𝔮 : Fin t.card → PrimeSpectrum B := fun i => (e i).1
  refine ⟨t.card, fun i => Localization.Away (f (𝔮 i)), fun i => inferInstance, fun i => inferInstance, fun i => inferInstance,
    fun i => inferInstance, fun i => IsLocalization.flat _ (Submonoid.powers (f (𝔮 i))), ?_,
    fun i => γ (𝔮 i), fun i => hγ (𝔮 i), fun i => hγℓ (𝔮 i), fun i => ?_⟩
  ·
    intro 𝔭
    obtain ⟨x, hx, hmem⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ 𝔭))
    have hrange : 𝔭 ∈ Set.range (PrimeSpectrum.comap (algebraMap B (Localization.Away (f x)))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (f x)) (f x)]
      exact hmem
    obtain ⟨𝔔, h𝔔⟩ := hrange
    have hex : e (e.symm ⟨x, hx⟩) = ⟨x, hx⟩ := e.apply_symm_apply _
    refine ⟨e.symm ⟨x, hx⟩, ?_⟩
    change ∃ 𝔔' : PrimeSpectrum (Localization.Away (f (e (e.symm ⟨x, hx⟩)).1)),
      PrimeSpectrum.comap (algebraMap B (Localization.Away (f (e (e.symm ⟨x, hx⟩)).1))) 𝔔' = 𝔭
    rw [hex]
    exact ⟨𝔔, h𝔔⟩
  ·
    exact H (𝔮 i) (Localization.Away (f (𝔮 i))) (IsScalarTower.toAlgHom 𝒪 B (Localization.Away (f (𝔮 i))))
      (IsLocalization.Away.algebraMap_isUnit (f (𝔮 i)))

end S_CerednikDrinfeld_QM_IsFineModuliT_exists_flat_family_isPullback_of_cerednikDrinfeld_uniformization_fine_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFineModuliT_exists_flat_family_isPullback_of_cerednikDrinfeld_uniformization_fine_eq (solution)
