-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsFineModuliT.existsUnique_factor_of_cerednikDrinfeld_uniformization_fine
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/cd23d5ed-a302-5f3a-b6d8-e388ebe16bae

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_AlgFunctorConst
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_CerednikDrinfeld_ClassSetGraph

import Theorems.Thm_CerednikDrinfeld_QM_exists_flat_family_lift_of_formallyEtale_of_locallyOfFiniteType
import Theorems.Thm_CerednikDrinfeld_QM_IsFineModuliT_exists_flat_family_isPullback_of_cerednikDrinfeld_uniformization_fine_eq
import Theorems.Thm_AlgebraicGeometry_existsUnique_forall_specMap_comp_eq_of_flat_of_forall_exists_comap_eq
import Theorems.Thm_CerednikDrinfeld_QM_IsFineModuliT_apply_eq_apply_of_isPullback_of_frobTwist_eq_of_invariant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsFineModuliT_existsUnique_factor_of_cerednikDrinfeld_uniformization_fine
p2m_attr_erase "instance" "CerednikDrinfeld.Omega.HolRingOf.instSMulCommClass CerednikDrinfeld.Omega.holRingAction CerednikDrinfeld.Omega.holRingSMulCommClass CerednikDrinfeld.Omega.HolRingOf.instAlgebra CerednikDrinfeld.Omega.HolRingOf.instCommRing CerednikDrinfeld.Omega.HolRingOf.instMulSemiringAction CerednikDrinfeld.Omega.holRingAlgebra CerednikDrinfeld.Omega.IsometricAut.instGroup CerednikDrinfeld.Omega.pglOmegaAction CerednikDrinfeld.Mumford.AmbientSemilinearAut.instGroup CerednikDrinfeld.Mumford.invariantFieldAlgebra CerednikDrinfeld.Mumford.invariantFieldOfAlgebra CerednikDrinfeld.FormalOmega.edgeQuot.instCommRing CerednikDrinfeld.FormalOmega.edgeQuot.instAlgebra CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"
p2m_attr_erase "simp" "CerednikDrinfeld.Mumford.vertexType_self CerednikDrinfeld.Mumford.mem_typePreserving_iff"

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.FormalOmega NeronModelInfra

open CategoryTheory.Limits

namespace Q4AuxT

theorem eq_of_forall_specMap_comp_eq {B : Type} [CommRing B] {k : ℕ} (B' : Fin k → Type)
    [∀ i, CommRing (B' i)] [∀ i, Algebra B (B' i)] [∀ i, Module.Flat B (B' i)]
    (hcov : ∀ 𝔭 : PrimeSpectrum B, ∃ (i : Fin k) (𝔮 : PrimeSpectrum (B' i)), 𝔮.comap (algebraMap B (B' i)) = 𝔭)
    {T : Scheme.{0}} (φ₁ φ₂ : Spec (CommRingCat.of B) ⟶ T)
    (h : ∀ i, Spec.map (CommRingCat.ofHom (algebraMap B (B' i))) ≫ φ₁ = Spec.map (CommRingCat.ofHom (algebraMap B (B' i))) ≫ φ₂) :
    φ₁ = φ₂ := by
  have hcomp : ∀ i j, (Algebra.TensorProduct.includeLeftRingHom : B' i →+* B' i ⊗[B] B' j).comp (algebraMap B (B' i)) =
      (Algebra.TensorProduct.includeRight : B' j →ₐ[B] B' i ⊗[B] B' j).toRingHom.comp (algebraMap B (B' j)) := by
    intro i j
    ext b
    simp [Algebra.TensorProduct.includeLeftRingHom, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
      Algebra.TensorProduct.one_def]
  obtain ⟨φ, -, huniq⟩ := AlgebraicGeometry.existsUnique_forall_specMap_comp_eq_of_flat_of_forall_exists_comap_eq
    B' hcov (T := T) (fun i => Spec.map (CommRingCat.ofHom (algebraMap B (B' i))) ≫ φ₁) (fun i j => by
      simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp])
  rw [huniq φ₁ fun i => rfl, huniq φ₂ fun i => (h i).symm]

theorem exists_prime_tensor {B : Type} [CommRing B] (D E : Type) [CommRing D] [CommRing E] [Algebra B D] [Algebra B E]
    (𝔓 : PrimeSpectrum D) (𝔮 : PrimeSpectrum E)
    (h : 𝔓.comap (algebraMap B D) = 𝔮.comap (algebraMap B E)) :
    ∃ 𝔔 : PrimeSpectrum (D ⊗[B] E), 𝔔.comap (Algebra.TensorProduct.includeLeftRingHom) = 𝔓 := by
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := Spec.map (CommRingCat.ofHom (algebraMap B D)))
    (g := Spec.map (CommRingCat.ofHom (algebraMap B E))) 𝔓 𝔮 (by rw [Spec.map_apply, Spec.map_apply]; exact h)
  refine ⟨(pullbackSpecIso B D E).hom z, ?_⟩
  have e := congrArg (fun φ : pullback (Spec.map (CommRingCat.ofHom (algebraMap B D)))
      (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶ Spec (CommRingCat.of D) => φ z) (pullbackSpecIso_hom_fst B D E)
  simp only [Scheme.Hom.comp_apply, hz] at e
  rw [Spec.map_apply] at e
  exact e

end Q4AuxT

namespace Q4AuxT

section tensor
variable {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
  (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra 𝒪 A₁] [Algebra 𝒪 A₂] [Algebra B A₁] [Algebra B A₂]
  [IsScalarTower 𝒪 B A₁] [IsScalarTower 𝒪 B A₂]

noncomputable def inl : A₁ →ₐ[𝒪] A₁ ⊗[B] A₂ :=
  (Algebra.TensorProduct.includeLeft : A₁ →ₐ[B] A₁ ⊗[B] A₂).restrictScalars 𝒪

noncomputable def inr : A₂ →ₐ[𝒪] A₁ ⊗[B] A₂ :=
  (Algebra.TensorProduct.includeRight : A₂ →ₐ[B] A₁ ⊗[B] A₂).restrictScalars 𝒪

theorem inl_toRingHom : (inl (𝒪 := 𝒪) (B := B) A₁ A₂).toRingHom = Algebra.TensorProduct.includeLeftRingHom := rfl

theorem inr_toRingHom :
    (inr (𝒪 := 𝒪) (B := B) A₁ A₂).toRingHom = (Algebra.TensorProduct.includeRight : A₂ →ₐ[B] A₁ ⊗[B] A₂).toRingHom := rfl

theorem inl_apply (a : A₁) : inl (𝒪 := 𝒪) (B := B) A₁ A₂ a = a ⊗ₜ 1 := rfl
theorem inr_apply (a : A₂) : inr (𝒪 := 𝒪) (B := B) A₁ A₂ a = 1 ⊗ₜ a := rfl

theorem inl_comp_eq_inr_comp :
    (inl (𝒪 := 𝒪) (B := B) A₁ A₂).comp (IsScalarTower.toAlgHom 𝒪 B A₁) =
      (inr (𝒪 := 𝒪) (B := B) A₁ A₂).comp (IsScalarTower.toAlgHom 𝒪 B A₂) := by
  apply AlgHom.ext
  intro b
  show algebraMap B A₁ b ⊗ₜ[B] (1 : A₂) = (1 : A₁) ⊗ₜ[B] algebraMap B A₂ b
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.tmul_smul]

end tensor

end Q4AuxT

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

    (hliftsurjℓ : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π)) (ψ : Onr →ₐ[𝒪] k)
        (y : (Scheme.nilpPoints fMℓ).obj k), ∃ (P : (Omega K₀ π).obj k) (g : G), Θfℓ k hk ((ψ, P), g) = y)
    :
    ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
          (ρ' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B → (Scheme.nilpPoints t).obj B),
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
            (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
            ρ' B' hB' ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map φ x) = (Scheme.nilpPoints t).map φ (ρ' B hB x)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : (ℍ[ℚ, a₁, b₁])ˣ) (hγ : γ ∈ Γt) (hγℓ : γ ∈ Γtℓ ℓ)
            (x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B) (g : G),
            OmegaNr.IsTwistedAct π Onr Fr vdet B ((Units.map (ι₀ : ℍ[ℚ, a₁, b₁] →* Matrix (Fin 2) (Fin 2) K₀)) γ) x x' → ρ' B hB (x', θt ⟨γ, hγ⟩ * g) = ρ' B hB (x, g)) →
          ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints fMℓ).obj B → (Scheme.nilpPoints t).obj B,
            (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
              (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (y : (Scheme.nilpPoints fMℓ).obj B),
              u B' hB' ((Scheme.nilpPoints fMℓ).map φ y) = (Scheme.nilpPoints t).map φ (u B hB y)) ∧
            (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B), u B hB (Θfℓ B hB x) = ρ' B hB x) ∧
            ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (Scheme.nilpPoints fMℓ).obj B → (Scheme.nilpPoints t).obj B,
              (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
                (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (y : (Scheme.nilpPoints fMℓ).obj B),
                u' B' hB' ((Scheme.nilpPoints fMℓ).map φ y) = (Scheme.nilpPoints t).map φ (u' B hB y)) →
              (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B), u' B hB (Θfℓ B hB x) = ρ' B hB x) →
              ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints fMℓ).obj B), u' B hB y = u B hB y := by
  intro T t ρ' hρnat hρinv
  classical

  have nilp_of : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (C : Type) [CommRing C] [Algebra 𝒪 C] (φ : B →ₐ[𝒪] C),
      IsNilpotent (algebraMap 𝒪 B π) → IsNilpotent (algebraMap 𝒪 C π) := by
    intro B _ _ C _ _ φ hBπ
    obtain ⟨m, hm⟩ := hBπ
    exact ⟨m, by rw [← φ.commutes, ← map_pow, hm, map_zero]⟩

  have ρnat1 : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (C : Type) [CommRing C] [Algebra 𝒪 C]
      (hB₀ : IsNilpotent (algebraMap 𝒪 B π)) (hC : IsNilpotent (algebraMap 𝒪 C π)) (φ : B →ₐ[𝒪] C) (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (ρ' B hB₀ x).1 = (ρ' C hC ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map φ x)).1 := by
    intro B _ _ C _ _ hB₀ hC φ x
    rw [hρnat B C hB₀ hC φ x]
    rfl

  have Θnat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (C : Type) [CommRing C] [Algebra 𝒪 C]
      (hB₀ : IsNilpotent (algebraMap 𝒪 B π)) (hC : IsNilpotent (algebraMap 𝒪 C π)) (φ : B →ₐ[𝒪] C) (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
      Θfℓ C hC ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map φ x) = (Scheme.nilpPoints fMℓ).map φ (Θfℓ B hB₀ x) := fun B _ _ C _ _ hB₀ hC φ x => hnatℓ B C hB₀ hC φ x

  have key_eq : ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] (hC : IsNilpotent (algebraMap 𝒪 C π)) (x₁ x₂ : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj C),
      Θfℓ C hC x₁ = Θfℓ C hC x₂ → (ρ' C hC x₁).1 = (ρ' C hC x₂).1 := by
    intro C _ _ hC x₁ x₂ hx
    obtain ⟨k, C', _, _, _, _, _, hcov, γ, hγ, hγℓ, hloc⟩ :=
      CerednikDrinfeld.QM.IsFineModuliT.exists_flat_family_isPullback_of_cerednikDrinfeld_uniformization_fine_eq hrr hrN hrbarN hN 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet hB Λ hΛ 𝒳 f pt h𝒳 n hn hrn hrbarn hnN M fM ptF hM G ρ χ hρ p hp hρp hp_pt 𝒴 g ptT h𝒴 d₀ d₁ hd₀f hd₁f hd₀ hd₁ ar arbar harf harbarf har harbar hdef Λ₁ R₁ hΛ₁ hR₁ hRΛ₁ n₁ hn₁ hS₁ ι₀ hι₀ v hv Γt hΓt s sf hs Γtℓ hΓtℓ wbar hwbar θt Θf ΘT hnat hG hinv het ℓ Mℓ fMℓ Θfℓ hnatℓ hinvℓ hetℓ hfibℓ hfMℓ C hC x₁.1 x₂.1 x₁.2 x₂.2 hx
    have hCi : ∀ i, IsNilpotent (algebraMap 𝒪 (C' i) π) :=
      fun i => nilp_of C (C' i) (IsScalarTower.toAlgHom 𝒪 C (C' i)) hC
    apply Q4AuxT.eq_of_forall_specMap_comp_eq C' hcov
    intro i
    obtain ⟨hPB, hψ, hg⟩ := hloc i
    have e1 := ρnat1 C (C' i) hC (hCi i) (IsScalarTower.toAlgHom 𝒪 C (C' i)) x₁
    have e2 := ρnat1 C (C' i) hC (hCi i) (IsScalarTower.toAlgHom 𝒪 C (C' i)) x₂
    change Spec.map (CommRingCat.ofHom (algebraMap C (C' i))) ≫ _ = _ at e1
    change Spec.map (CommRingCat.ofHom (algebraMap C (C' i))) ≫ _ = _ at e2
    rw [e1, e2]
    have hi := CerednikDrinfeld.QM.IsFineModuliT.apply_eq_apply_of_isPullback_of_frobTwist_eq_of_invariant hrr hrN hrbarN hN 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet hB Λ hΛ 𝒳 f pt h𝒳 n hn hrn hrbarn hnN M fM ptF hM G ρ χ hρ p hp hρp hp_pt 𝒴 g ptT h𝒴 d₀ d₁ hd₀f hd₁f hd₀ hd₁ ar arbar harf harbarf har harbar hdef Λ₁ R₁ hΛ₁ hR₁ hRΛ₁ n₁ hn₁ hS₁ ι₀ hι₀ v hv Γt hΓt s sf hs Γtℓ hΓtℓ wbar hwbar θt Θf ΘT hnat hG hinv het ℓ T t ρ' hρnat hρinv (C' i) (hCi i)
      ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map (IsScalarTower.toAlgHom 𝒪 C (C' i)) x₁) ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map (IsScalarTower.toAlgHom 𝒪 C (C' i)) x₂) (γ i) (hγ i) (hγℓ i)
      hPB hψ hg
    exact (congrArg Subtype.val hi).symm

  haveI : LocallyOfFiniteType fMℓ := hfMℓ
  have hQ1 := CerednikDrinfeld.QM.exists_flat_family_lift_of_formallyEtale_of_locallyOfFiniteType 𝒪 hdvr π hπ hres hunr K₀ Onr hOnr_max hOnr_alg G Mℓ fMℓ Θfℓ hnatℓ hetℓ hliftsurjℓ
  choose kf Bf iCR iAO iAB iST iFl hcovf hBf xf hxf using hQ1

  have hdesc : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB₀ : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints fMℓ).obj B),
      ∃ φ : Spec (CommRingCat.of B) ⟶ T, ∀ i,
        Spec.map (CommRingCat.ofHom (algebraMap B (Bf B hB₀ y i))) ≫ φ = (ρ' (Bf B hB₀ y i) (hBf B hB₀ y i) (xf B hB₀ y i)).1 := by
    intro B _ _ hB₀ y
    letI := iCR B hB₀ y; letI := iAO B hB₀ y; letI := iAB B hB₀ y
    haveI := iST B hB₀ y; haveI := iFl B hB₀ y
    obtain ⟨φ, hφ, -⟩ := AlgebraicGeometry.existsUnique_forall_specMap_comp_eq_of_flat_of_forall_exists_comap_eq
      (Bf B hB₀ y) (hcovf B hB₀ y) (T := T) (fun i => (ρ' (Bf B hB₀ y i) (hBf B hB₀ y i) (xf B hB₀ y i)).1) (by
        intro i j

        have hij : IsNilpotent (algebraMap 𝒪 (Bf B hB₀ y i ⊗[B] Bf B hB₀ y j) π) :=
          nilp_of _ _ (Q4AuxT.inl (𝒪 := 𝒪) (B := B) (Bf B hB₀ y i) (Bf B hB₀ y j)) (hBf B hB₀ y i)
        have l1 := ρnat1 _ _ (hBf B hB₀ y i) hij (Q4AuxT.inl (𝒪 := 𝒪) (B := B) (Bf B hB₀ y i) (Bf B hB₀ y j)) (xf B hB₀ y i)
        have l2 := ρnat1 _ _ (hBf B hB₀ y j) hij (Q4AuxT.inr (𝒪 := 𝒪) (B := B) (Bf B hB₀ y i) (Bf B hB₀ y j)) (xf B hB₀ y j)
        rw [Q4AuxT.inl_toRingHom] at l1
        rw [Q4AuxT.inr_toRingHom] at l2
        rw [l1, l2]
        apply key_eq
        rw [Θnat _ _ (hBf B hB₀ y i) hij, Θnat _ _ (hBf B hB₀ y j) hij, hxf, hxf, ← (Scheme.nilpPoints fMℓ).map_comp, ← (Scheme.nilpPoints fMℓ).map_comp,
          Q4AuxT.inl_comp_eq_inr_comp])
    exact ⟨φ, hφ⟩
  choose uval huval using hdesc

  have char : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB₀ : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints fMℓ).obj B)
      (D : Type) [CommRing D] [Algebra 𝒪 D] (hD : IsNilpotent (algebraMap 𝒪 D π)) (φ : B →ₐ[𝒪] D) (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj D),
      Θfℓ D hD x = (Scheme.nilpPoints fMℓ).map φ y → Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ uval B hB₀ y = (ρ' D hD x).1 := by
    intro B _ _ hB₀ y D _ _ hD φ x hx
    letI := iCR B hB₀ y; letI := iAO B hB₀ y; letI := iAB B hB₀ y
    haveI := iST B hB₀ y; haveI := iFl B hB₀ y
    letI : Algebra B D := φ.toRingHom.toAlgebra
    haveI : IsScalarTower 𝒪 B D := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm

    let Df : Fin (kf B hB₀ y) → Type := fun i => D ⊗[B] Bf B hB₀ y i
    have hcovD : ∀ 𝔓 : PrimeSpectrum D, ∃ (i : Fin (kf B hB₀ y)) (𝔔 : PrimeSpectrum (Df i)), 𝔔.comap (algebraMap D (Df i)) = 𝔓 := by
      intro 𝔓
      obtain ⟨i, 𝔮, h𝔮⟩ := hcovf B hB₀ y (𝔓.comap (algebraMap B D))
      obtain ⟨𝔔, h𝔔⟩ := Q4AuxT.exists_prime_tensor (B := B) D (Bf B hB₀ y i) 𝔓 𝔮 h𝔮.symm
      exact ⟨i, 𝔔, h𝔔⟩
    apply Q4AuxT.eq_of_forall_specMap_comp_eq (B := D) Df hcovD
    intro i
    have hDi : IsNilpotent (algebraMap 𝒪 (Df i) π) := nilp_of D (Df i) (IsScalarTower.toAlgHom 𝒪 D (Df i)) hD

    have r1 := ρnat1 D (Df i) hD hDi (IsScalarTower.toAlgHom 𝒪 D (Df i)) x
    change Spec.map (CommRingCat.ofHom (algebraMap D (Df i))) ≫ _ = _ at r1
    rw [r1]

    have sq : (IsScalarTower.toAlgHom 𝒪 D (Df i)).comp φ =
        (Q4AuxT.inr (𝒪 := 𝒪) (B := B) D (Bf B hB₀ y i)).comp (IsScalarTower.toAlgHom 𝒪 B (Bf B hB₀ y i)) := by
      have := Q4AuxT.inl_comp_eq_inr_comp (𝒪 := 𝒪) (B := B) D (Bf B hB₀ y i)
      exact this
    have sq' : Spec.map (CommRingCat.ofHom (algebraMap D (Df i))) ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) =
        Spec.map (CommRingCat.ofHom (Q4AuxT.inr (𝒪 := 𝒪) (B := B) D (Bf B hB₀ y i)).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap B (Bf B hB₀ y i))) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact congrArg AlgHom.toRingHom sq
    rw [← Category.assoc, sq', Category.assoc, huval B hB₀ y i,
      ρnat1 _ _ (hBf B hB₀ y i) hDi (Q4AuxT.inr (𝒪 := 𝒪) (B := B) D (Bf B hB₀ y i)) (xf B hB₀ y i)]
    apply key_eq
    rw [Θnat D (Df i) hD hDi, Θnat _ _ (hBf B hB₀ y i) hDi, hxf, hx, ← (Scheme.nilpPoints fMℓ).map_comp, ← (Scheme.nilpPoints fMℓ).map_comp, sq]

  have hover : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB₀ : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints fMℓ).obj B),
      uval B hB₀ y ≫ t = Scheme.specOver (𝒪 := 𝒪) B := by
    intro B _ _ hB₀ y
    letI := iCR B hB₀ y; letI := iAO B hB₀ y; letI := iAB B hB₀ y
    haveI := iST B hB₀ y; haveI := iFl B hB₀ y
    apply Q4AuxT.eq_of_forall_specMap_comp_eq (Bf B hB₀ y) (hcovf B hB₀ y)
    intro i
    rw [← Category.assoc, huval B hB₀ y i, (ρ' (Bf B hB₀ y i) (hBf B hB₀ y i) (xf B hB₀ y i)).2]
    exact (Scheme.specMap_algHom_comp_specOver (IsScalarTower.toAlgHom 𝒪 B (Bf B hB₀ y i))).symm

  refine ⟨fun B _ _ hB₀ y => ⟨uval B hB₀ y, hover B hB₀ y⟩, ?_, ?_, ?_⟩
  ·
    intro B _ _ C _ _ hB₀ hC φ y
    apply Subtype.ext
    show uval C hC ((Scheme.nilpPoints fMℓ).map φ y) = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ uval B hB₀ y
    letI := iCR C hC ((Scheme.nilpPoints fMℓ).map φ y); letI := iAO C hC ((Scheme.nilpPoints fMℓ).map φ y); letI := iAB C hC ((Scheme.nilpPoints fMℓ).map φ y)
    haveI := iST C hC ((Scheme.nilpPoints fMℓ).map φ y); haveI := iFl C hC ((Scheme.nilpPoints fMℓ).map φ y)
    apply Q4AuxT.eq_of_forall_specMap_comp_eq (Bf C hC ((Scheme.nilpPoints fMℓ).map φ y)) (hcovf C hC ((Scheme.nilpPoints fMℓ).map φ y))
    intro i
    rw [huval C hC ((Scheme.nilpPoints fMℓ).map φ y) i, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    symm
    have := char B hB₀ y (Bf C hC ((Scheme.nilpPoints fMℓ).map φ y) i) (hBf C hC ((Scheme.nilpPoints fMℓ).map φ y) i)
      ((IsScalarTower.toAlgHom 𝒪 C (Bf C hC ((Scheme.nilpPoints fMℓ).map φ y) i)).comp φ) (xf C hC ((Scheme.nilpPoints fMℓ).map φ y) i)
      (by rw [hxf, ← (Scheme.nilpPoints fMℓ).map_comp])
    exact this
  ·
    intro B _ _ hB₀ x
    apply Subtype.ext
    show uval B hB₀ (Θfℓ B hB₀ x) = (ρ' B hB₀ x).1
    have := char B hB₀ (Θfℓ B hB₀ x) B hB₀ (AlgHom.id 𝒪 B) x (by rw [(Scheme.nilpPoints fMℓ).map_id])
    rw [← this]
    show uval B hB₀ (Θfℓ B hB₀ x) = Spec.map (CommRingCat.ofHom (RingHom.id B)) ≫ uval B hB₀ (Θfℓ B hB₀ x)
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  ·
    intro u' hu'nat hu'fac B _ _ hB₀ y
    apply Subtype.ext
    show (u' B hB₀ y).1 = uval B hB₀ y
    letI := iCR B hB₀ y; letI := iAO B hB₀ y; letI := iAB B hB₀ y
    haveI := iST B hB₀ y; haveI := iFl B hB₀ y
    apply Q4AuxT.eq_of_forall_specMap_comp_eq (Bf B hB₀ y) (hcovf B hB₀ y)
    intro i
    rw [huval B hB₀ y i]
    have n1 := hu'nat B (Bf B hB₀ y i) hB₀ (hBf B hB₀ y i) (IsScalarTower.toAlgHom 𝒪 B (Bf B hB₀ y i)) y
    have n2 := congrArg Subtype.val n1
    change _ = Spec.map (CommRingCat.ofHom (algebraMap B (Bf B hB₀ y i))) ≫ (u' B hB₀ y).1 at n2
    rw [← n2, ← hxf B hB₀ y i, hu'fac]

end S_CerednikDrinfeld_QM_IsFineModuliT_existsUnique_factor_of_cerednikDrinfeld_uniformization_fine
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsFineModuliT_existsUnique_factor_of_cerednikDrinfeld_uniformization_fine (solution)
