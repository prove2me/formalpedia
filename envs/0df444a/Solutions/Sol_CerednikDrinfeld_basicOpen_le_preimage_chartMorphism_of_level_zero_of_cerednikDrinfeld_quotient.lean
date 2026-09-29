-- Prove2me | solution 1 for CerednikDrinfeld.basicOpen_le_preimage_chartMorphism_of_level_zero_of_cerednikDrinfeld_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/81a928eb-e51f-5990-847f-42362a1c9f8c

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_basicOpen_le_preimage_chartMorphism_of_level_zero_of_cerednikDrinfeld_quotient
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
p2m_open "CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld P2MW.S_CerednikDrinfeld_basicOpen_le_preimage_chartMorphism_of_level_zero_of_cerednikDrinfeld_quotient.CerednikDrinfeld CerednikDrinfeld.FormalOmega"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "tree"
namespace ChartPreimageLevel
p2m_open "CerednikDrinfeld"

theorem base_specMap_factorₐ_bot {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {I 𝔮 : Ideal A} [𝔮.IsPrime]
    (hI : I ≤ 𝔮) (𝔭 : PrimeSpectrum (A ⧸ I)) (h𝔮 : ∀ a : A, a ∈ 𝔮 ↔ Ideal.Quotient.mk I a ∈ 𝔭.asIdeal) :
    PrimeSpectrum.comap (Ideal.Quotient.factorₐ R hI).toRingHom (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (A ⧸ 𝔮)) = 𝔭 := by
  apply PrimeSpectrum.ext
  rw [PrimeSpectrum.comap_asIdeal]
  ext a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [Ideal.mem_comap, Ideal.mem_bot, ← h𝔮, ← Ideal.Quotient.eq_zero_iff_mem]
  rfl

theorem base_specMap_factorₐ_bot_mem_basicOpen {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {I 𝔮 : Ideal A}
    [𝔮.IsPrime] (hI : I ≤ 𝔮) (t : A) (ht : t ∉ 𝔮) :
    PrimeSpectrum.comap (Ideal.Quotient.factorₐ R hI).toRingHom (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (A ⧸ 𝔮)) ∈
      PrimeSpectrum.basicOpen (Ideal.Quotient.mk I t) := by
  rw [PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, Ideal.mem_bot]
  change ¬ (Ideal.Quotient.mk 𝔮 t = 0)
  rwa [Ideal.Quotient.eq_zero_iff_mem]

theorem mem_preimage_preimage_of_comp_eq {S Y₁ Y₂ X₁ X₂ Z : Scheme} {a₁ : S ⟶ Y₁} {κ₁ : Y₁ ⟶ X₁} {p₁ : X₁ ⟶ Z}
    {a₂ : S ⟶ Y₂} {κ₂ : Y₂ ⟶ X₂} {p₂ : X₂ ⟶ Z} (heq : a₁ ≫ κ₁ ≫ p₁ = a₂ ≫ κ₂ ≫ p₂) (V : Z.Opens) (y : S)
    {x : Y₁} (hx : a₁.base y = x) (h : a₂.base y ∈ κ₂ ⁻¹ᵁ (p₂ ⁻¹ᵁ V)) : x ∈ κ₁ ⁻¹ᵁ (p₁ ⁻¹ᵁ V) := by
  subst hx
  change (a₁ ≫ κ₁ ≫ p₁).base y ∈ (V : Set Z)
  rw [heq]
  exact h

end CerednikDrinfeld.ChartPreimageLevel

open CerednikDrinfeld.ChartPreimageLevel

theorem solution

    {r : ℕ} [Fact r.Prime]
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

    (G : Type) [Group G] (σ : G →* Matrix.GeneralLinearGroup (Fin 2) K₀) (Γ : Subgroup G)
    (hcent : ∃ z ∈ Γ, ∃ c : K₀, ((σ z : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀) = c • (1 : Matrix (Fin 2) (Fin 2) K₀) ∧
      vdet (σ z) = Multiplicative.ofAdd (2 : ℤ))
    (hodd : ∃ w ∈ Γ, vdet (σ w) = Multiplicative.ofAdd (1 : ℤ))
    (Γ' : Subgroup G) (hΓ' : ∀ x : G, x ∈ Γ' ↔ x ∈ Γ ∧ Even (Multiplicative.toAdd (vdet (σ x))))

    (ρ : G →* PGL(2, K₀)) (hρ : ∀ g : G, ρ g = Matrix.ProjGenLinGroup.mk (σ g))
    (hdisc : ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, Set.Finite {g : PGL(2, K₀) | g ∈ Γ'.map ρ ∧ g • v = v})
    (hcocpt : ∃ S : Finset (LT.LatticeTree.Vertex 𝒪 K₀), ∀ v : LT.LatticeTree.Vertex 𝒪 K₀, ∃ g ∈ Γ'.map ρ, g • v ∈ S)

    (𝒳 : Scheme.{0}) (f : 𝒳 ⟶ Spec (CommRingCat.of 𝒪)) [IsProper f] [Flat f]

    (Θ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints f).obj B)
    (hΘnat : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      Θ B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints f).map φ (Θ B hB x))
    (hΘinv : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : G), γ ∈ Γ →
      ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
        OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) x x' → Θ B hB x' = Θ B hB x)
    (hΘfib : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra 𝒪 k] (hk : IsNilpotent (algebraMap 𝒪 k π)) (ψ : Onr →ₐ[𝒪] k),
      (∀ y : (Scheme.nilpPoints f).obj k, ∃ P : (Omega K₀ π).obj k, Θ k hk (ψ, P) = y) ∧
      ∀ P P' : (Omega K₀ π).obj k, Θ k hk (ψ, P) = Θ k hk (ψ, P') ↔
        ∃ γ ∈ Γ, OmegaNr.IsTwistedAct π Onr Fr vdet k (σ γ) (ψ, P) (ψ, P'))
    (hΘuniv : ∀ (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of 𝒪))
      (ρ' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
        (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints t).obj B),
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
        (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
        ρ' B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints t).map φ (ρ' B hB x)) →
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (γ : G), γ ∈ Γ →
        ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
          OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) x x' → ρ' B hB x' = ρ' B hB x) →
      ∃ u : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
          (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B,
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (y : (Scheme.nilpPoints f).obj B),
          u B' hB' ((Scheme.nilpPoints f).map φ y) = (Scheme.nilpPoints t).map φ (u B hB y)) ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), u B hB (Θ B hB x) = ρ' B hB x) ∧
        ∀ u' : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
            (Scheme.nilpPoints f).obj B → (Scheme.nilpPoints t).obj B,
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π))
            (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (y : (Scheme.nilpPoints f).obj B),
            u' B' hB' ((Scheme.nilpPoints f).map φ y) = (Scheme.nilpPoints t).map φ (u' B hB y)) →
          (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
            (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), u' B hB (Θ B hB x) = ρ' B hB x) →
          ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (y : (Scheme.nilpPoints f).obj B),
            u' B hB y = u B hB y)
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
        (sn : ∀ n : ℕ, Spec (CommRingCat.of (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)})) ⟶ Spec (CommRingCat.of 𝒪))
        (hsn : ∀ n : ℕ, sn n = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}))))
    (κ : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), Spec (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})) ⟶ Limits.pullback f (sn n))
    (hκ : (∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ)
          (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra Onr B] [IsScalarTower 𝒪 Onr B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (xbar : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) →ₐ[Onr] B) (d P : DeligneDatum (K := K₀) π B),
          (d.line (stdFullLattice K₀) =
              Submodule.span B {(xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
            d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
              (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
                (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
            d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
          DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d P →
          (Θ B hB ((IsScalarTower.toAlgHom 𝒪 Onr B), P)).1 =
            Spec.map (CommRingCat.ofHom xbar.toRingHom) ≫ κ h n ≫ Limits.pullback.fst f (sn n)))
    (V : 𝒳.Opens) (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (t : chartERing Onr (algebraMap 𝒪 Onr π) r)
    (ht₀ : PrimeSpectrum.basicOpen (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (0 + 1)}) t) ≤ (κ h 0) ⁻¹ᵁ ((Limits.pullback.fst f (sn 0)) ⁻¹ᵁ V))
    (n : ℕ) :
    PrimeSpectrum.basicOpen (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) t) ≤ (κ h n) ⁻¹ᵁ ((Limits.pullback.fst f (sn n)) ⁻¹ᵁ V) := by
  classical
  haveI := hdvr
  intro 𝔭 h𝔭
  rw [PrimeSpectrum.mem_basicOpen] at h𝔭

  obtain ⟨𝔮, h𝔮def⟩ : ∃ 𝔮 : Ideal (chartERing Onr (algebraMap 𝒪 Onr π) r), 𝔮 =
      𝔭.asIdeal.comap (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})) :=
    ⟨_, rfl⟩
  haveI h𝔮 : 𝔮.IsPrime := by rw [h𝔮def]; exact Ideal.comap_isPrime _ _
  have hmem𝔮 : ∀ a : chartERing Onr (algebraMap 𝒪 Onr π) r, a ∈ 𝔮 ↔
      Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) a ∈ 𝔭.asIdeal :=
    fun a => by rw [h𝔮def, Ideal.mem_comap]
  have hIn : Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)} ≤ 𝔮 := by
    intro a ha
    rw [hmem𝔮, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact zero_mem _
  have hϖ𝔮 : algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π) ∈ 𝔮 :=
    h𝔮.mem_of_pow_mem (n + 1) (hIn (Ideal.subset_span (Set.mem_singleton _)))
  have hI0 : Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (0 + 1)} ≤ 𝔮 := by
    rw [Ideal.span_le, Set.singleton_subset_iff, zero_add, pow_one]
    exact hϖ𝔮
  have ht𝔮 : t ∉ 𝔮 := fun ht => h𝔭 ((hmem𝔮 t).mp ht)

  letI instAlg : Algebra 𝒪 (chartERing Onr (algebraMap 𝒪 Onr π) r ⧸ 𝔮) :=
    ((algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r ⧸ 𝔮)).comp (algebraMap 𝒪 Onr)).toAlgebra
  haveI instTower : @IsScalarTower 𝒪 Onr (chartERing Onr (algebraMap 𝒪 Onr π) r ⧸ 𝔮)
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq (R := 𝒪) (S := Onr) (A := chartERing Onr (algebraMap 𝒪 Onr π) r ⧸ 𝔮) (fun _ => rfl)
  have halg : ∀ a : 𝒪, algebraMap 𝒪 (chartERing Onr (algebraMap 𝒪 Onr π) r ⧸ 𝔮) a =
      Ideal.Quotient.mk 𝔮 (algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr a)) := fun _ => rfl
  have hB : IsNilpotent (algebraMap 𝒪 (chartERing Onr (algebraMap 𝒪 Onr π) r ⧸ 𝔮) π) := by
    rw [halg, Ideal.Quotient.eq_zero_iff_mem.mpr hϖ𝔮]
    exact IsNilpotent.zero

  let ptB := (chartE Onr (algebraMap 𝒪 Onr π) r).map (Ideal.Quotient.mkₐ Onr 𝔮) (chartERing.point Onr (algebraMap 𝒪 Onr π) r)
  let pt : (chartE 𝒪 π r).obj (chartERing Onr (algebraMap 𝒪 Onr π) r ⧸ 𝔮) :=
    ⟨(Ideal.Quotient.mk 𝔮 (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r), Ideal.Quotient.mk 𝔮 (chartERing.η Onr (algebraMap 𝒪 Onr π) r)),
      ptB.2.1, ptB.2.2.1, ptB.2.2.2⟩
  obtain ⟨d, hd1, hd2, hd3⟩ := exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent π hπ r hres g₁ hg₁
    (chartERing Onr (algebraMap 𝒪 Onr π) r ⧸ 𝔮) hB (chartERing.lift pt)
  simp only [chartERing.lift_ξ] at hd1
  simp only [chartERing.lift_η] at hd2
  have hP := DeligneDatum.isPullback_pullback π (chartERing Onr (algebraMap 𝒪 Onr π) r ⧸ 𝔮) h⁻¹ d

  have en := hκ h n (chartERing Onr (algebraMap 𝒪 Onr π) r ⧸ 𝔮) hB (Ideal.Quotient.factorₐ Onr hIn) d _ ⟨hd1, hd2, hd3⟩ hP
  have e0 := hκ h 0 (chartERing Onr (algebraMap 𝒪 Onr π) r ⧸ 𝔮) hB (Ideal.Quotient.factorₐ Onr hI0) d _ ⟨hd1, hd2, hd3⟩ hP
  have heq := en.symm.trans e0

  exact mem_preimage_preimage_of_comp_eq heq V ((⟨⊥, Ideal.isPrime_bot⟩ :
      PrimeSpectrum (chartERing Onr (algebraMap 𝒪 Onr π) r ⧸ 𝔮)))
    (base_specMap_factorₐ_bot (R := Onr) hIn 𝔭 hmem𝔮)
    (ht₀ (base_specMap_factorₐ_bot_mem_basicOpen (R := Onr) hI0 t ht𝔮))

end S_CerednikDrinfeld_basicOpen_le_preimage_chartMorphism_of_level_zero_of_cerednikDrinfeld_quotient
end P2MW
export P2MW.S_CerednikDrinfeld_basicOpen_le_preimage_chartMorphism_of_level_zero_of_cerednikDrinfeld_quotient (solution)
