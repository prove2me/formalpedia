-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFineModuli.existsUnique_factor_of_cerednikDrinfeld_uniformization_tower_of_isUnit_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/e3488092-5954-5fb4-99e9-cee4f75ed6d1

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_AlgFunctorConst
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Theorems.Thm_CerednikDrinfeld_QM_IsFineModuliT_existsUnique_factor_of_cerednikDrinfeld_uniformization_fine
import Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing
import Theorems.Thm_AlgebraicGeometry_Scheme_locallyOfFiniteType_of_quotient_of_isNoetherianRing
import Theorems.Thm_CerednikDrinfeld_FormalOmega_AlgFunctor_formalQuotient_descent
import Theorems.Thm_CerednikDrinfeld_FormalOmega_OmegaNr_isTwistedAct_laws
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuli_existsUnique_factor_of_cerednikDrinfeld_uniformization_tower_of_isUnit_two
p2m_attr_erase "instance" "CerednikDrinfeld.Omega.HolRingOf.instSMulCommClass CerednikDrinfeld.Omega.holRingAction CerednikDrinfeld.Omega.holRingSMulCommClass CerednikDrinfeld.Omega.HolRingOf.instAlgebra CerednikDrinfeld.Omega.HolRingOf.instCommRing CerednikDrinfeld.Omega.HolRingOf.instMulSemiringAction CerednikDrinfeld.Omega.holRingAlgebra CerednikDrinfeld.Omega.IsometricAut.instGroup CerednikDrinfeld.Omega.pglOmegaAction CerednikDrinfeld.Mumford.AmbientSemilinearAut.instGroup CerednikDrinfeld.Mumford.invariantFieldAlgebra CerednikDrinfeld.Mumford.invariantFieldOfAlgebra CerednikDrinfeld.FormalOmega.edgeQuot.instCommRing CerednikDrinfeld.FormalOmega.edgeQuot.instAlgebra CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"
p2m_attr_erase "simp" "CerednikDrinfeld.Mumford.vertexType_self CerednikDrinfeld.Mumford.mem_typePreserving_iff"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega NeronModelInfra

open CategoryTheory.Limits

namespace QUTowerAux

theorem finite_of_isLevelTwistAction {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {N m : ℕ} [NeZero m]
    {B : Type} [CommRing B] {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of B)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      FakeEllipticCurve.WithFullLevel Λ N m S → SchemeHomOver s πM}
    {G : Type} [Group G] {ρ : G →* Aut M} {χ : G → ↥Λ} (hρ : IsLevelTwistAction Λ N m M πM ptF G ρ χ) : Finite G := by
  classical
  set I : Ideal ℤ := Ideal.span {(m : ℤ)} with hI
  haveI : Module.Finite ℤ ↥Λ := Module.Finite.iff_fg.mpr hΛ.fg
  haveI : Finite (ℤ ⧸ I) := Finite.of_equiv (ZMod m) (Int.quotientSpanNatEquivZMod m).symm.toEquiv
  haveI : Module.Finite (ℤ ⧸ I) (↥Λ ⧸ (I • ⊤ : Submodule ℤ ↥Λ)) := inferInstance
  haveI : Finite (↥Λ ⧸ (I • ⊤ : Submodule ℤ ↥Λ)) := Module.finite_of_finite (ℤ ⧸ I)
  refine Finite.of_injective (fun g => Submodule.Quotient.mk (p := (I • ⊤ : Submodule ℤ ↥Λ)) (χ g)) ?_
  intro g g' hgg'
  apply hρ.label_injective g g'
  have hmem : χ g - χ g' ∈ (I • ⊤ : Submodule ℤ ↥Λ) := (Submodule.Quotient.eq _).mp hgg'
  rw [hI, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨y, _, hy⟩ := hmem
  refine ⟨y, ?_⟩
  have := congrArg (fun z : ↥Λ => (z : ℍ[ℚ, a, b])) hy
  simp only [Submodule.coe_sub] at this
  rw [← this, Submodule.coe_smul_of_tower, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast]

end QUTowerAux

theorem solution

    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrN : ¬ r ∣ N) (hrbarN : ¬ rbar ∣ N) (hN : Squarefree N)

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (h2 : IsUnit ((2 : ℕ) : 𝒪))
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
    :

    ∀ (ℓ : HeckeTower.AwayPrime r rbar)

      (Mℓ : Scheme.{0}) (fMℓ : Mℓ ⟶ Spec (CommRingCat.of 𝒪))
      (ptFℓ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithFullLevel Λ N n S),
        u.1.ExtraLevel (ℓ.1 : ℕ) → SchemeHomOver s fMℓ)
      (hMℓ : IsFineModuliT Λ N n (ℓ.1 : ℕ) Mℓ fMℓ ptFℓ)
      (πℓ : Mℓ ⟶ M) (hπℓf : πℓ ≫ fM = fMℓ)
      (hπℓ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithFullLevel Λ N n S)
        (C : u.1.ExtraLevel (ℓ.1 : ℕ)), (ptFℓ S s u C).1 ≫ πℓ = (ptF S s u).1)
      (pℓ : Mℓ ⟶ 𝒴 ℓ) (hpℓg : pℓ ≫ g ℓ = fMℓ)
      (hpℓ : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithFullLevel Λ N n S)
        (C : u.1.ExtraLevel (ℓ.1 : ℕ)), (ptFℓ S s u C).1 ≫ pℓ = (ptT ℓ S s ⟨u.1, C⟩).1)
      (ρℓ : G →* Aut Mℓ) (hρℓf : ∀ h : G, (ρℓ h).hom ≫ fMℓ = fMℓ)
      (hρℓπ : ∀ h : G, (ρℓ h).hom ≫ πℓ = πℓ ≫ (ρ h).hom) (hρℓp : ∀ h : G, (ρℓ h).hom ≫ pℓ = pℓ)
      (hρℓtw : ∀ (h : G) (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪))
        (u u' : FakeEllipticCurve.WithFullLevel Λ N n S) (C : u.1.ExtraLevel (ℓ.1 : ℕ)) (C' : u'.1.ExtraLevel (ℓ.1 : ℕ))
        (e : u.1.A ≅ u'.1.A) (he : e.hom ≫ u'.1.f = u.1.f),
        FakeEllipticCurve.WithFullLevel.IsTwistVia (χ h) u u' e he →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
            FactorsThrough C.levK P ↔ FactorsThrough C'.levK (mapPt e.hom he P)) →
          (ptFℓ S s u' C').1 = (ptFℓ S s u C).1 ≫ (ρℓ h).hom)

      (Θfℓ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B → (Scheme.nilpPoints fMℓ).obj B)

      (hnatℓ :
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
          Θfℓ B' hB' ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map φ x) = (Scheme.nilpPoints fMℓ).map φ (Θfℓ B hB x)))

      (hGℓ :
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B) (g h : G),
          (Scheme.nilpPoints.mapHom fMℓ fMℓ (ρℓ h).hom (hρℓf h)).app B (Θfℓ B hB (x, g * h)) = Θfℓ B hB (x, g)))

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

      (hπℓΘ :
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
          (Scheme.nilpPoints.mapHom fMℓ fM πℓ hπℓf).app B (Θfℓ B hB x) = Θf B hB x))

      (hpℓΘ :
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
          (Scheme.nilpPoints.mapHom fMℓ (g ℓ) pℓ hpℓg).app B (Θfℓ B hB (x, (1 : G))) = ΘT ℓ B hB x))

      (hfMℓ : LocallyOfFiniteType fMℓ)

      (Xℓ' : Scheme.{0}) (πℓ' : Mℓ ⟶ Xℓ') (hπℓ' : ∀ h : G, (ρℓ h).hom ≫ πℓ' = πℓ')
      (hintℓ' : IsIntegralHom πℓ') (haffℓ' : IsAffineHom πℓ') (hsurjℓ' : Function.Surjective πℓ'.base)
      (hsecℓ' : ∀ V : Xℓ'.Opens, Function.Injective (πℓ'.app V))
      (hinvℓ' : ∀ V : Xℓ'.Opens, Set.range (πℓ'.app V) =
        {s | ∀ h : G, (ρℓ h).hom.appLE (πℓ' ⁻¹ᵁ V) (πℓ' ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπℓ' h]) s = s})
      (hopenℓ' : ∀ U : Mℓ.Opens, IsAffineOpen U → (∀ h : G, (ρℓ h).hom ⁻¹ᵁ U = U) → ∃ V : Xℓ'.Opens, IsAffineOpen V ∧ πℓ' ⁻¹ᵁ V = U)
      (πXℓ' : Xℓ' ⟶ Spec (CommRingCat.of 𝒪)) (hπXℓ' : πℓ' ≫ πXℓ' = fMℓ)
      (eXℓ : Xℓ' ⟶ 𝒴 ℓ) (heXℓiso : IsIso eXℓ) (heXℓ : eXℓ ≫ g ℓ = πXℓ') (hpeℓ : πℓ' ≫ eXℓ = pℓ)

      (hliftsurjℓ : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π)) (ψ : Onr →ₐ[𝒪] k)
          (y : (Scheme.nilpPoints fMℓ).obj k), ∃ (P : (Omega K₀ π).obj k) (g : G), Θfℓ k hk ((ψ, P), g) = y),
      (∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
          (ρ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints t).obj B),
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
            (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), ρ B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints t).map φ (ρ B hB x)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : (ℍ[ℚ, a₁, b₁])ˣ), γ ∈ Γtℓ ℓ →
            ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B, OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ) x x' → ρ B hB x' = ρ B hB x) →
          ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints (g ℓ)).obj B → (Scheme.nilpPoints t).obj B,
            (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
              (φ : B →ₐ[𝒪] B') (y : (Scheme.nilpPoints (g ℓ)).obj B), u B' hB' ((Scheme.nilpPoints (g ℓ)).map φ y) = (Scheme.nilpPoints t).map φ (u B hB y)) ∧
            (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), u B hB (ΘT ℓ B hB x) = ρ B hB x) ∧
            ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints (g ℓ)).obj B → (Scheme.nilpPoints t).obj B,
              (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
                (φ : B →ₐ[𝒪] B') (y : (Scheme.nilpPoints (g ℓ)).obj B), u' B' hB' ((Scheme.nilpPoints (g ℓ)).map φ y) = (Scheme.nilpPoints t).map φ (u' B hB y)) →
              (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), u' B hB (ΘT ℓ B hB x) = ρ B hB x) →
              ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints (g ℓ)).obj B), u' B hB y = u B hB y) := by
  intro ℓ Mℓ fMℓ ptFℓ hMℓ πℓ hπℓf hπℓ pℓ hpℓg hpℓ ρℓ hρℓf hρℓπ hρℓp hρℓtw Θfℓ hnatℓ hGℓ hinvℓ hetℓ hfibℓ hπℓΘ hpℓΘ hfMℓ
    Xℓ' πℓ' hπℓ' hintℓ' haffℓ' hsurjℓ' hsecℓ' hinvℓ' hopenℓ' πXℓ' hπXℓ' eXℓ heXℓiso heXℓ hpeℓ hliftsurjℓ T t ρT hρTnat hρTinv
  classical
  haveI := hdvr
  haveI : IsNoetherianRing 𝒪 := inferInstance
  haveI : NeZero n := ⟨by omega⟩
  haveI hGfin : Finite G := QUTowerAux.finite_of_isLevelTwistAction hΛ.isOrder hρ
  haveI : IsIso eXℓ := heXℓiso

  have hii_b := CerednikDrinfeld.QM.IsFineModuliT.existsUnique_factor_of_cerednikDrinfeld_uniformization_fine
    hrr hrN hrbarN hN 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet hB Λ hΛ
    𝒳 f pt h𝒳 n hn hrn hrbarn hnN M fM ptF hM G ρ χ hρ p hp hρp hp_pt 𝒴 g ptT h𝒴 d₀ d₁ hd₀f hd₁f hd₀ hd₁ ar arbar harf harbarf
    har harbar hdef Λ₁ R₁ hΛ₁ hR₁ hRΛ₁ n₁ hn₁ hS₁ ι₀ hι₀ v hv Γt hΓt s sf hs Γtℓ hΓtℓ wbar hwbar θt Θf ΘT hnat hG hinv het
    ℓ Mℓ fMℓ Θfℓ hnatℓ hinvℓ hetℓ hfibℓ hfMℓ hliftsurjℓ

  let ΓL : Subgroup (ℍ[ℚ, a₁, b₁])ˣ := Γt ⊓ Γtℓ ℓ
  let θL : ↥ΓL → G := fun γ => θt ⟨(γ : (ℍ[ℚ, a₁, b₁])ˣ), γ.2.1⟩
  have hθL_one : θL 1 = 1 := by
    show θt ⟨((1 : ↥ΓL) : (ℍ[ℚ, a₁, b₁])ˣ), (1 : ↥ΓL).2.1⟩ = 1
    have : (⟨((1 : ↥ΓL) : (ℍ[ℚ, a₁, b₁])ˣ), (1 : ↥ΓL).2.1⟩ : ↥Γt) = 1 := rfl
    rw [this, map_one]
  have hθL_mul : ∀ γ γ' : ↥ΓL, θL (γ * γ') = θL γ * θL γ' := by
    intro γ γ'
    show θt ⟨((γ * γ' : ↥ΓL) : (ℍ[ℚ, a₁, b₁])ˣ), (γ * γ').2.1⟩ = θt ⟨(γ : (ℍ[ℚ, a₁, b₁])ˣ), γ.2.1⟩ * θt ⟨(γ' : (ℍ[ℚ, a₁, b₁])ˣ), γ'.2.1⟩
    rw [← map_mul]
    rfl
  let Γ : Type := ↥ΓL × G
  let act : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], Γ → (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B → (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B → Prop :=
    fun B _ _ γh xg xg' =>
      OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) (γh.1 : (ℍ[ℚ, a₁, b₁])ˣ)) xg.1 xg'.1 ∧
        @Eq G xg'.2 (@HMul.hMul G G G _ (@HMul.hMul G G G _ (θL γh.1) xg.2) (γh.2)⁻¹)
  let Γ' : Subgroup Γ := (⊤ : Subgroup ↥ΓL).prod ⊥
  let a : Γ → (Mℓ ⟶ Mℓ) := fun γh => (ρℓ γh.2).hom
  have ha_over : ∀ γh : Γ, a γh ≫ fMℓ = fMℓ := fun γh => hρℓf γh.2
  have ha_p : ∀ γh : Γ, a γh ≫ pℓ = pℓ := fun γh => hρℓp γh.2
  have ha_one : ∀ γh : Γ, γh ∈ Γ' → a γh = 𝟙 Mℓ := by
    intro γh hγh
    have h2 : γh.2 = 1 := (Subgroup.mem_prod.mp hγh).2
    show (ρℓ γh.2).hom = 𝟙 Mℓ
    rw [h2, map_one]
    rfl
  have ha_mul : ∀ γ γ' : Γ, a (γ' * γ) = a γ ≫ a γ' := by
    intro γ γ'
    show (ρℓ (γ' * γ).2).hom = (ρℓ γ.2).hom ≫ (ρℓ γ'.2).hom
    rw [Prod.snd_mul, map_mul]
    rfl

  obtain ⟨hRfun, hRtot, hRone, hRmul, hRnat, -, -, -⟩ := CerednikDrinfeld.FormalOmega.OmegaNr.isTwistedAct_laws π Onr Fr vdet
  have hιmul : ∀ γ γ' : Γ, (Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) ((γ' * γ).1 : (ℍ[ℚ, a₁, b₁])ˣ) =
      (Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) (γ'.1 : (ℍ[ℚ, a₁, b₁])ˣ) * (Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) (γ.1 : (ℍ[ℚ, a₁, b₁])ˣ) := by
    intro γ γ'; rw [Prod.fst_mul, Subgroup.coe_mul, map_mul]
  have hact_fun : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (γ : Γ) (x x' x'' : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B), act B γ x x' → act B γ x x'' → x' = x'' := by
    intro B _ _ γ x x' x'' h1 h2
    exact Prod.ext (hRfun B _ x.1 x'.1 x''.1 h1.1 h2.1) (h1.2.trans h2.2.symm)
  have hact_total : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (γ : Γ) (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B), ∃ x', act B γ x x' := by
    intro B _ _ γ x
    obtain ⟨y, hy⟩ := hRtot B ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) (γ.1 : (ℍ[ℚ, a₁, b₁])ˣ)) x.1
    exact ⟨(y, (@HMul.hMul G G G _ (@HMul.hMul G G G _ (θL γ.1) x.2) (γ.2)⁻¹ : G)), hy, rfl⟩
  have hact_one : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B), act B 1 x x := by
    intro B _ _ x
    refine ⟨?_, ?_⟩
    · show OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) ((1 : Γ).1 : (ℍ[ℚ, a₁, b₁])ˣ)) x.1 x.1
      rw [Prod.fst_one, Subgroup.coe_one, map_one]; exact hRone B x.1
    · show @Eq G x.2 (@HMul.hMul G G G _ (@HMul.hMul G G G _ (θL (1 : Γ).1) x.2) ((1 : Γ).2)⁻¹)
      rw [Prod.fst_one, Prod.snd_one, hθL_one, one_mul, inv_one, mul_one]
  have hact_mul : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (γ γ' : Γ) (x y z : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B), act B γ x y → act B γ' y z → act B (γ' * γ) x z := by
    intro B _ _ γ γ' x y z hxy hyz
    refine ⟨?_, ?_⟩
    · show OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) ((γ' * γ).1 : (ℍ[ℚ, a₁, b₁])ˣ)) x.1 z.1
      rw [hιmul]; exact hRmul B _ _ x.1 y.1 z.1 hxy.1 hyz.1
    · show @Eq G z.2 (@HMul.hMul G G G _ (@HMul.hMul G G G _ (θL (γ' * γ).1) x.2) ((γ' * γ).2)⁻¹)
      have e1 : @Eq G y.2 _ := hxy.2
      have e2 : @Eq G z.2 _ := hyz.2
      rw [e2, e1, Prod.fst_mul, Prod.snd_mul, hθL_mul, mul_inv_rev]
      simp only [mul_assoc]
  have hact_nat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B') (γ : Γ)
      (x x' : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B), act B γ x x' → act B' γ ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map φ x) ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map φ x') := by
    intro B _ _ B' _ _ φ γ x x' h
    exact ⟨hRnat B B' φ _ x.1 x'.1 h.1, h.2⟩

  have hΘf_eqv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : Γ) (x x' : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
      act B γ x x' → Θfℓ B hB x' = (Scheme.nilpPoints.mapHom fMℓ fMℓ (a γ) (ha_over γ)).app B (Θfℓ B hB x) := by
    intro B _ _ hB γ x x' hx
    obtain ⟨htw, hg'⟩ := hx
    obtain ⟨x₁, g₁⟩ := x
    obtain ⟨x₁', g₁'⟩ := x'
    change G at g₁ g₁'
    simp only at htw hg'
    have h1 := hGℓ B hB x₁ (g₁ * (γ.2)⁻¹) γ.2
    rw [inv_mul_cancel_right] at h1
    have h2 := hinvℓ B hB (γ.1 : (ℍ[ℚ, a₁, b₁])ˣ) γ.1.2.1 γ.1.2.2 x₁ x₁' (g₁ * (γ.2)⁻¹) htw
    show Θfℓ B hB (x₁', g₁') = (Scheme.nilpPoints.mapHom fMℓ fMℓ (ρℓ γ.2).hom (hρℓf γ.2)).app B (Θfℓ B hB (x₁, g₁))
    rw [h1, ← h2, hg', mul_assoc]

  have hinvX : inv eXℓ ≫ πXℓ' = g ℓ := by
    rw [← heXℓ, IsIso.inv_hom_id_assoc]
  have hlftX' : LocallyOfFiniteType πXℓ' :=
    AlgebraicGeometry.Scheme.locallyOfFiniteType_of_quotient_of_isNoetherianRing fMℓ πXℓ' hfMℓ ρℓ πℓ' hπXℓ' hπℓ' hintℓ' haffℓ' hsurjℓ'
      hsecℓ' hinvℓ' hopenℓ'
  have hF1 : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (y : (Scheme.nilpPoints fMℓ).obj B),
      (Scheme.nilpPoints.mapHom (g ℓ) πXℓ' (inv eXℓ) hinvX).app B ((Scheme.nilpPoints.mapHom fMℓ (g ℓ) pℓ hpℓg).app B y) =
        (Scheme.nilpPoints.mapHom fMℓ πXℓ' πℓ' hπXℓ').app B y := by
    intro B _ _ y
    apply Subtype.ext
    show (y.1 ≫ pℓ) ≫ inv eXℓ = y.1 ≫ πℓ'
    rw [← hpeℓ, Category.assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hF2 : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (y : (Scheme.nilpPoints fMℓ).obj B),
      (Scheme.nilpPoints.mapHom πXℓ' (g ℓ) eXℓ heXℓ).app B ((Scheme.nilpPoints.mapHom fMℓ πXℓ' πℓ' hπXℓ').app B y) =
        (Scheme.nilpPoints.mapHom fMℓ (g ℓ) pℓ hpℓg).app B y := by
    intro B _ _ y
    apply Subtype.ext
    show (y.1 ≫ πℓ') ≫ eXℓ = y.1 ≫ pℓ
    rw [Category.assoc, hpeℓ]
  have hF3 : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (z : (Scheme.nilpPoints (g ℓ)).obj B),
      (Scheme.nilpPoints.mapHom πXℓ' (g ℓ) eXℓ heXℓ).app B ((Scheme.nilpPoints.mapHom (g ℓ) πXℓ' (inv eXℓ) hinvX).app B z) = z := by
    intro B _ _ z
    apply Subtype.ext
    show (z.1 ≫ inv eXℓ) ≫ eXℓ = z.1
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hp_univ : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
      (ρ' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints fMℓ).obj B → (Scheme.nilpPoints t).obj B),
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
        (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints fMℓ).obj B), ρ' B' hB' ((Scheme.nilpPoints fMℓ).map φ x) = (Scheme.nilpPoints t).map φ (ρ' B hB x)) →
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : Γ) (y : (Scheme.nilpPoints fMℓ).obj B),
        ρ' B hB ((Scheme.nilpPoints.mapHom fMℓ fMℓ (a γ) (ha_over γ)).app B y) = ρ' B hB y) →
      ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints (g ℓ)).obj B → (Scheme.nilpPoints t).obj B,
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
          (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints (g ℓ)).obj B), u B' hB' ((Scheme.nilpPoints (g ℓ)).map φ x) = (Scheme.nilpPoints t).map φ (u B hB x)) ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints fMℓ).obj B),
          u B hB ((Scheme.nilpPoints.mapHom fMℓ (g ℓ) pℓ hpℓg).app B y) = ρ' B hB y) ∧
        ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints (g ℓ)).obj B → (Scheme.nilpPoints t).obj B,
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
            (φ : B →ₐ[𝒪] B') (x : (Scheme.nilpPoints (g ℓ)).obj B), u' B' hB' ((Scheme.nilpPoints (g ℓ)).map φ x) = (Scheme.nilpPoints t).map φ (u' B hB x)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints fMℓ).obj B),
            u' B hB ((Scheme.nilpPoints.mapHom fMℓ (g ℓ) pℓ hpℓg).app B y) = ρ' B hB y) →
          ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (z : (Scheme.nilpPoints (g ℓ)).obj B), u' B hB z = u B hB z := by
    intro T t ρ' hρ'nat hρ'inv
    obtain ⟨ubar, hub_nat, hub_fac, hub_uniq⟩ :=
      AlgebraicGeometry.Scheme.existsUnique_nilpPoints_factor_of_quotient_of_isNoetherianRing π fMℓ πXℓ' hfMℓ hlftX' ρℓ
        hρℓf πℓ' hπXℓ' hπℓ' hintℓ' haffℓ' hsurjℓ' hsecℓ' hinvℓ' T t ρ' hρ'nat
        (fun B _ _ hB h y => hρ'inv B hB ((1 : ↥ΓL), h) y)
    refine ⟨fun B _ _ hB z => ubar B hB ((Scheme.nilpPoints.mapHom (g ℓ) πXℓ' (inv eXℓ) hinvX).app B z), ?_, ?_, ?_⟩
    · intro B _ _ B' _ _ hB hB' φ x
      show ubar B' hB' ((Scheme.nilpPoints.mapHom (g ℓ) πXℓ' (inv eXℓ) hinvX).app B' ((Scheme.nilpPoints (g ℓ)).map φ x)) = _
      rw [(Scheme.nilpPoints.mapHom (g ℓ) πXℓ' (inv eXℓ) hinvX).naturality φ x, hub_nat]
    · intro B _ _ hB y
      show ubar B hB ((Scheme.nilpPoints.mapHom (g ℓ) πXℓ' (inv eXℓ) hinvX).app B ((Scheme.nilpPoints.mapHom fMℓ (g ℓ) pℓ hpℓg).app B y)) = _
      rw [hF1, hub_fac]
    · intro u' hu'nat hu'fac B _ _ hB z
      have huniq := hub_uniq (fun B _ _ hB w => u' B hB ((Scheme.nilpPoints.mapHom πXℓ' (g ℓ) eXℓ heXℓ).app B w))
        (fun B _ _ B' _ _ hB hB' φ w => by
          show u' B' hB' ((Scheme.nilpPoints.mapHom πXℓ' (g ℓ) eXℓ heXℓ).app B' ((Scheme.nilpPoints πXℓ').map φ w)) = _
          rw [(Scheme.nilpPoints.mapHom πXℓ' (g ℓ) eXℓ heXℓ).naturality φ w, hu'nat])
        (fun B _ _ hB y => by
          show u' B hB ((Scheme.nilpPoints.mapHom πXℓ' (g ℓ) eXℓ heXℓ).app B ((Scheme.nilpPoints.mapHom fMℓ πXℓ' πℓ' hπXℓ').app B y)) = _
          rw [hF2, hu'fac])
      have h1 := huniq B hB ((Scheme.nilpPoints.mapHom (g ℓ) πXℓ' (inv eXℓ) hinvX).app B z)
      simp only [hF3] at h1
      exact h1

  obtain ⟨hAnat, hAinv, hAuniv⟩ := CerednikDrinfeld.FormalOmega.AlgFunctor.formalQuotient_descent 𝒪 π (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)) Γ act
    hact_fun hact_total hact_one hact_mul hact_nat Γ' Mℓ (𝒴 ℓ) fMℓ (g ℓ) pℓ hpℓg a ha_over ha_p ha_one ha_mul hp_univ Θfℓ hnatℓ hΘf_eqv
    (by
      intro T' t' ρ' hρ'nat hρ'inv
      exact hii_b T' t' ρ' hρ'nat (fun B _ _ hB γ hγ hγℓ x x' g' htw =>
        hρ'inv B hB ((⟨γ, ⟨hγ, hγℓ⟩⟩ : ↥ΓL), 1) (Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, Subgroup.mem_bot.mpr rfl⟩) (x, g') (x', θt ⟨γ, hγ⟩ * g')
          ⟨htw, by simp [θL]⟩))

  let Θ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints (g ℓ)).obj B :=
    fun B _ _ hB x => (Scheme.nilpPoints.mapHom fMℓ (g ℓ) pℓ hpℓg).app B (Θfℓ B hB (x, (1 : G)))
  have hsheet : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B) (g' : G),
      (Scheme.nilpPoints.mapHom fMℓ (g ℓ) pℓ hpℓg).app B (Θfℓ B hB (x, g')) = Θ B hB x := by
    intro B _ _ hB x g'
    have h1 := hGℓ B hB x 1 g'
    rw [one_mul] at h1
    apply Subtype.ext
    show (Θfℓ B hB (x, g')).1 ≫ pℓ = (Θfℓ B hB (x, (1 : G))).1 ≫ pℓ
    rw [← h1]
    show _ = ((Θfℓ B hB (x, g')).1 ≫ (ρℓ g').hom) ≫ pℓ
    rw [Category.assoc, hρℓp]
  have hΘT : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      Θ B hB x = ΘT ℓ B hB x := fun B _ _ hB x => hpℓΘ B hB x

  obtain ⟨u, hu_nat, hu_fac, hu_uniq⟩ := hAuniv T t (fun B _ _ hB xg => ρT B hB xg.1)
    (fun B _ _ B' _ _ hB hB' φ xg => hρTnat B B' hB hB' φ xg.1)
    (fun B _ _ hB γ xg xg' hx => hρTinv B hB (γ.1 : (ℍ[ℚ, a₁, b₁])ˣ) γ.1.2.2 xg.1 xg'.1 hx.1)
  refine ⟨u, hu_nat, fun B _ _ hB x => ?_, ?_⟩
  · rw [← hΘT]
    exact hu_fac B hB (x, (1 : G))
  · intro u' hu'_nat hu'_fac B _ _ hB z
    exact hu_uniq u' hu'_nat (fun B _ _ hB xg => by
      obtain ⟨x, g'⟩ := xg
      change G at g'
      show u' B hB ((Scheme.nilpPoints.mapHom fMℓ (g ℓ) pℓ hpℓg).app B (Θfℓ B hB (x, g'))) = ρT B hB x
      rw [hsheet, hΘT]; exact hu'_fac B hB x) B hB z

end S_CerednikDrinfeld_QM_IsFineModuli_existsUnique_factor_of_cerednikDrinfeld_uniformization_tower_of_isUnit_two
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFineModuli_existsUnique_factor_of_cerednikDrinfeld_uniformization_tower_of_isUnit_two (solution)
