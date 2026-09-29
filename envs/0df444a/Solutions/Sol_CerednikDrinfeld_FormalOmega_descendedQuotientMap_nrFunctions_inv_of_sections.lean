-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.descendedQuotientMap_nrFunctions_inv_of_sections
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/4a21d613-e295-503d-b70e-bf1e23bf21e6

import Definitions.Def_CerednikDrinfeld_FormalQuotientDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordTower
import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum
import Definitions.Def_CerednikDrinfeld_MumfordNrPresentation
import Theorems.Thm_CerednikDrinfeld_FormalOmega_OmegaNr_isTwistedAct_laws
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_nrFunctions_inv_of_sections

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in
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

    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])

    (N : Subgroup (PGL(2, K₀))) (hNle : N ≤ Γ'.map ρ) (hNnorm : (N.subgroupOf (Γ.map ρ)).Normal) (hNidx : N.relIndex (Γ'.map ρ) ≠ 0)
    (DM : MumfordTower 𝒪 π K₀ r g₁ N)

    (X : ℕ → Scheme.{0}) (xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))
    (xt : ∀ n : ℕ, X n ⟶ X (n + 1))
    (G₂ : Type) [Group G₂] [Finite G₂] (a : ∀ n : ℕ, G₂ →* Aut (X n))
    (pr₁ : ∀ n : ℕ, X n ⟶ DM.Z n) (pr₂ : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})))
    (θ : ↥Γ →* G₂) (Fr₂ : ∀ n : ℕ, (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) ≃ₐ[𝒪] (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}))
    (hcart : ∀ n : ℕ, IsPullback (xt n) (xb n) (xb (n + 1)) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π (Nat.le_succ (n + 1))))))))
    (hproper : ∀ n : ℕ, IsProper (xb n)) (hflat : ∀ n : ℕ, Flat (xb n))
    (haff : ∀ (n : ℕ) (S : Set (X n)), S.Finite → ∃ U : (X n).Opens, IsAffineOpen U ∧ S ⊆ (U : Set (X n)))
    (ha_over : ∀ (n : ℕ) (g : G₂), (a n g).hom ≫ xb n = xb n)
    (ha_xt : ∀ (n : ℕ) (g : G₂), (a n g).hom ≫ xt n = xt n ≫ (a (n + 1) g).hom)
    (hX : ∀ n : ℕ, IsPullback (pr₁ n) (pr₂ n) (DM.zb n) (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)))
            (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))))
    (hxb : ∀ n : ℕ, xb n = pr₁ n ≫ DM.zb n)
    (hxt₁ : ∀ n : ℕ, xt n ≫ pr₁ (n + 1) = pr₁ n ≫ DM.zt n)
    (hxt₂ : ∀ n : ℕ, xt n ≫ pr₂ (n + 1) = pr₂ n ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) (Nat.le_succ (n + 1)))))))
    (hθsurj : Function.Surjective θ) (hθker : ∀ γ : ↥Γ, θ γ = 1 ↔ ρ (γ : G) ∈ N)
    (hFr₂ : ∀ (n : ℕ) (y y' : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))), (y' : Onr) = Fr (y : Onr) →
      Fr₂ n (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ y')
    (ha_pr₂ : ∀ (n : ℕ) (γ : ↥Γ), (a n (θ γ)).hom ≫ pr₂ n =
      pr₂ n ≫ Spec.map (CommRingCat.ofHom ((Fr₂ n) ^ (- Multiplicative.toAdd (vdet (σ (γ : G))))).toRingEquiv.toRingHom))
    (ha_pr₁ : ∀ (n : ℕ) (γ : ↥Γ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
      (P P' : (Omega K₀ π).obj B), DeligneDatum.IsPullback (K := K₀) (π := π) B (σ (γ : G))⁻¹ P P' →
      ∀ x : Spec (CommRingCat.of B) ⟶ X n, x ≫ pr₁ n = DM.q n B hB P → (x ≫ (a n (θ γ)).hom) ≫ pr₁ n = DM.q n B hB P')

    (DQ : TowerQuotientDatum 𝒪 π X xb xt G₂ a)
    (q : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B], (algebraMap 𝒪 B π) ^ (n + 1) = 0 →
    (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Spec (CommRingCat.of B) ⟶ DQ.Y n))
    (hqdef : (∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (ψ : Onr →ₐ[𝒪] B)
        (ψ₂ : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) →ₐ[𝒪] B) (hψ₂ : ∀ y : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)), ψ₂ (Ideal.Quotient.mk _ y) = ψ (y : Onr))
        (P : (Omega K₀ π).obj B) (x : Spec (CommRingCat.of B) ⟶ X n),
        x ≫ pr₁ n = DM.q n B hB P → x ≫ pr₂ n = Spec.map (CommRingCat.ofHom ψ₂.toRingHom) → q n B hB (ψ, P) = x ≫ DQ.p n))
    (hqover : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
    (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
    q n B hB x ≫ DQ.yb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
      Spec.map (CommRingCat.ofHom (algebraMap 𝒪 B)))
    (hqnat : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
    (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (hB' : (algebraMap 𝒪 B' π) ^ (n + 1) = 0) (φ : B →ₐ[𝒪] B')
    (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
    q n B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ q n B hB x)
    (hqyt : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
    (hB' : (algebraMap 𝒪 B π) ^ (n + 1 + 1) = 0) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
    q (n + 1) B hB' x = q n B hB x ≫ DQ.yt n)
    (hqinv : ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0) (γ : G), γ ∈ Γ →
    ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
      OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) x x' → q n B hB x' = q n B hB x)

    (Pr : MumfordTower.NrPresentation 𝒪 π K₀ g₁ N DM Onr Fr X xb xt G₂ a pr₁ pr₂ ((Γ'.subgroupOf Γ).map θ))
    (D' : TowerQuotientDatum Onr (algebraMap 𝒪 Onr π) Pr.X' Pr.xb' Pr.xt' G₂ Pr.a')
    (rY : ∀ n : ℕ, D'.Y n ⟶ DQ.Y n)
    (hrY : ∀ n : ℕ, IsPullback (rY n) (D'.yb n) (DQ.yb n)
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) (algebraMap 𝒪 Onr)
        (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))))
    (hrY_p : ∀ n : ℕ, D'.p n ≫ rY n = Pr.qX n ≫ DQ.p n)
    (hrY_yt : ∀ n : ℕ, D'.yt n ≫ rY (n + 1) = rY n ≫ DQ.yt n)

    (U : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), (D'.Y n).Opens)
    (hU : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), (U h n : Set (D'.Y n)) = Set.range (Pr.κ' h n ≫ D'.p n).base)
    (c : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ),
      ↑((D'.Y n).presheaf.obj (Opposite.op (U h n))) →+* ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}))
    (hκU : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ), (Pr.κ' h n ≫ D'.p n) ⁻¹ᵁ (U h n) = ⊤)
    (hc : ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ)
      (hle : (⊤ : (Spec (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}))).Opens) ≤ (Pr.κ' h n ≫ D'.p n) ⁻¹ᵁ (U h n))
      (s : ↑((D'.Y n).presheaf.obj (Opposite.op (U h n)))),
      c h n s = (Scheme.ΓSpecIso (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}))).hom.hom
        ((Spec (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}))).presheaf.map (homOfLE hle).op (((Pr.κ' h n ≫ D'.p n).app (U h n)).hom s)))
    (h : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (fam : ∀ m : ℕ, ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}))
    (hfam : (∀ m : ℕ, Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
              (pow_dvd_pow (algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) (Nat.le_succ (m + 1)))) (fam (m + 1)) = fam m))
    (s : ∀ m : ℕ, ↑((D'.Y m).presheaf.obj (Opposite.op (U h m))))
    (hs : (∀ (m : ℕ) (hle : U h m ≤ (D'.yt m) ⁻¹ᵁ (U h (m + 1))),
        (D'.Y m).presheaf.map (homOfLE hle).op (((D'.yt m).app (U h (m + 1))).hom (s (m + 1))) = s m))
    (hsc : ∀ m : ℕ, c h m (s m) = fam m)
    :
    ∀ (m : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra Onr B] [IsScalarTower 𝒪 Onr B],
              IsNilpotent (algebraMap 𝒪 B π) →
              ∀ (xbar xbar' : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) →ₐ[Onr] B) (d d' P P' : DeligneDatum (K := K₀) π B),
                (d.line (stdFullLattice K₀) =
              Submodule.span B {(xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
            d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
              (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
                (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
            d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
                (d'.line (stdFullLattice K₀) =
              Submodule.span B {(xbar' (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
            d'.line (FullLattice.act g₁ (stdFullLattice K₀)) =
              (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (xbar' (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
                (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
            d'.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
                DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d P →
                DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d' P' →
                (∃ γ ∈ Γ', DeligneDatum.IsPullback (K := K₀) (π := π) B (σ γ)⁻¹ P P') →
                xbar (fam m) = xbar' (fam m) := by
  intro m B _ _ _ _ hBnil xbar xbar' d d' P P' hd hd' hP hP' hrel
  classical

  have hBm : (algebraMap 𝒪 B π) ^ (m + 1) = 0 := by
    rw [IsScalarTower.algebraMap_apply 𝒪 Onr B π, ← xbar.commutes, ← map_pow]
    have h0 : (algebraMap Onr ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (algebraMap 𝒪 Onr π)) ^ (m + 1) = 0 := by
      show (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π))) ^ (m + 1) = 0
      rw [← RingHom.map_pow (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)})), Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _
    rw [h0, map_zero]

  let ψB : Onr →ₐ[𝒪] B := IsScalarTower.toAlgHom 𝒪 Onr B

  have F1 : ∃ γ ∈ Γ, OmegaNr.IsTwistedAct π Onr Fr vdet B (σ γ) (ψB, P) (ψB, P') := by
    obtain ⟨γ, hγ', hPP'⟩ := hrel
    obtain ⟨hγΓ, heven⟩ := (hΓ' γ).mp hγ'
    obtain ⟨k, hk⟩ := heven
    obtain ⟨z, hzΓ, c, hzc, hzdet⟩ := hcent

    have hc0 : c ≠ 0 := by
      intro h0
      have hdet : ((σ z : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀).det = 0 := by
        rw [hzc, h0, zero_smul, Matrix.det_zero]
      apply (Matrix.GeneralLinearGroup.det (σ z)).ne_zero
      rw [Matrix.GeneralLinearGroup.val_det_apply]
      exact hdet
    have hzs : σ z = scalarGL (Units.mk0 c hc0) := by
      apply Units.ext
      rw [hzc, scalarGL_coe]
      rfl

    have hscal : ∀ (u : K₀ˣ) (Q : DeligneDatum (K := K₀) π B), DeligneDatum.IsPullback (K := K₀) (π := π) B (scalarGL u) Q Q := by
      intro u Q M
      rw [Q.homothety u M, Submodule.comap_map_eq_of_injective (actBaseChange B (scalarGL u) M).injective]

    obtain ⟨-, -, -, -, -, -, -, hcomp⟩ := CerednikDrinfeld.FormalOmega.OmegaNr.isTwistedAct_laws (K₀ := K₀) π Onr Fr vdet
    refine ⟨z ^ (-(k : ℤ)) * γ, Γ.mul_mem (Γ.zpow_mem hzΓ _) hγΓ, ?_, ?_⟩
    ·
      have hv : Multiplicative.toAdd (vdet (σ (z ^ (-(k : ℤ)) * γ))) = 0 := by
        rw [map_mul, map_mul, map_zpow, map_zpow, hzdet, toAdd_mul, toAdd_zpow, hk]
        simp only [toAdd_ofAdd, smul_eq_mul]
        ring
      show ψB = frobTwist Onr Fr (- Multiplicative.toAdd (vdet (σ (z ^ (-(k : ℤ)) * γ)))) ψB
      rw [hv, neg_zero]
      ext y
      simp [frobTwist]
    ·
      show DeligneDatum.IsPullback (K := K₀) (π := π) B (σ (z ^ (-(k : ℤ)) * γ))⁻¹ P P'
      rw [map_mul, map_zpow, hzs]
      let sHom : K₀ˣ →* Matrix.GeneralLinearGroup (Fin 2) K₀ :=
        { toFun := scalarGL, map_one' := scalarGL_one, map_mul' := scalarGL_mul }
      have h2 : DeligneDatum.IsPullback (K := K₀) (π := π) B ((scalarGL (Units.mk0 c hc0)) ^ (-(k : ℤ)))⁻¹ P' P' := by
        rw [← zpow_neg, neg_neg, show scalarGL (Units.mk0 c hc0) = sHom (Units.mk0 c hc0) from rfl, ← map_zpow]
        exact hscal _ P'
      exact hcomp B (σ γ) ((scalarGL (Units.mk0 c hc0)) ^ (-(k : ℤ))) P P' P' hPP' h2

  have F2 : Spec.map (CommRingCat.ofHom xbar.toRingHom) ≫ Pr.κ' h m ≫ D'.p m =
      Spec.map (CommRingCat.ofHom xbar'.toRingHom) ≫ Pr.κ' h m ≫ D'.p m := by

    have himg : ∀ (x : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) →ₐ[Onr] B) (dd PP : DeligneDatum (K := K₀) π B),
        (dd.line (stdFullLattice K₀) =
              Submodule.span B {(x (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
            dd.line (FullLattice.act g₁ (stdFullLattice K₀)) =
              (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (x (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
                (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
            dd.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
        DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ dd PP →
        (Spec.map (CommRingCat.ofHom x.toRingHom) ≫ Pr.κ' h m ≫ D'.p m) ≫ rY m = q m B hBm (ψB, PP) := by
      intro x dd PP hdd hPP

      let ψ₂ : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (m + 1)}) →ₐ[𝒪] B :=
        { toRingHom := x.toRingHom.comp (Ideal.quotientMap (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) ((algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r)).comp ((AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val.toRingHom))
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))
          commutes' := fun a => by
            show x.toRingHom ((Ideal.quotientMap (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) ((algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r)).comp ((AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val.toRingHom))
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)) (algebraMap 𝒪 (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (m + 1)}) a)) = algebraMap 𝒪 B a
            rw [← Ideal.Quotient.mk_algebraMap, Ideal.quotientMap_mk, RingHom.comp_apply, IsScalarTower.algebraMap_apply 𝒪 Onr B a]
            have hy : ((AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val.toRingHom (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) a) : Onr) = algebraMap 𝒪 Onr a :=
              (AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val.commutes a
            rw [hy]
            exact x.commutes (algebraMap 𝒪 Onr a) }
      have hψ₂ : ∀ y : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)), ψ₂ (Ideal.Quotient.mk _ y) = ψB (y : Onr) := by
        intro y
        show x.toRingHom ((Ideal.quotientMap (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) ((algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r)).comp ((AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val.toRingHom))
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)) (Ideal.Quotient.mk _ y)) = algebraMap Onr B (y : Onr)
        rw [Ideal.quotientMap_mk, RingHom.comp_apply]
        exact x.commutes (y : Onr)
      have h1 : (Spec.map (CommRingCat.ofHom x.toRingHom) ≫ Pr.κ' h m ≫ Pr.qX m) ≫ pr₁ m = DM.q m B hBm PP := by
        simp only [Category.assoc]
        exact Pr.κ'_pr₁ h m B hBm x dd PP hdd hPP
      have h2 : (Spec.map (CommRingCat.ofHom x.toRingHom) ≫ Pr.κ' h m ≫ Pr.qX m) ≫ pr₂ m = Spec.map (CommRingCat.ofHom ψ₂.toRingHom) := by
        simp only [Category.assoc]
        rw [Pr.κ'_pr₂ h m, ← Spec.map_comp]
        rfl
      rw [Category.assoc, Category.assoc, hrY_p m, hqdef m B hBm ψB ψ₂ hψ₂ PP _ h1 h2]
      simp only [Category.assoc]
    obtain ⟨γ, hγ, htw⟩ := F1
    have hY : (Spec.map (CommRingCat.ofHom xbar.toRingHom) ≫ Pr.κ' h m ≫ D'.p m) ≫ rY m =
        (Spec.map (CommRingCat.ofHom xbar'.toRingHom) ≫ Pr.κ' h m ≫ D'.p m) ≫ rY m := by
      rw [himg xbar d P hd hP, himg xbar' d' P' hd' hP', hqinv m B hBm γ hγ (ψB, P) (ψB, P') htw]
    have hring : CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r))
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)) ≫ CommRingCat.ofHom xbar.toRingHom =
        CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r))
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)) ≫ CommRingCat.ofHom xbar'.toRingHom := by
      apply CommRingCat.hom_ext
      apply Ideal.Quotient.ringHom_ext
      apply RingHom.ext
      intro y
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, Ideal.quotientMap_mk]
      exact (xbar.commutes y).trans (xbar'.commutes y).symm
    have hb : (Spec.map (CommRingCat.ofHom xbar.toRingHom) ≫ Pr.κ' h m ≫ D'.p m) ≫ D'.yb m =
        (Spec.map (CommRingCat.ofHom xbar'.toRingHom) ≫ Pr.κ' h m ≫ D'.p m) ≫ D'.yb m := by
      simp only [Category.assoc]
      rw [D'.p_over m, Pr.κ'_xb' h m, ← Spec.map_comp, ← Spec.map_comp, hring]
    exact (hrY m).hom_ext hY hb

  have hpre : ∀ (x : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) →ₐ[Onr] B),
      (⊤ : (Spec (CommRingCat.of B)).Opens) ≤ (Spec.map (CommRingCat.ofHom x.toRingHom) ≫ Pr.κ' h m ≫ D'.p m) ⁻¹ᵁ (U h m) := by
    intro x
    rw [Scheme.Hom.comp_preimage, hκU]
    exact le_top
  have F3 : ∀ (x : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) →ₐ[Onr] B),
      x (c h m (s m)) =
        (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom
          ((Spec (CommRingCat.of B)).presheaf.map (homOfLE (hpre x)).op
            (((Spec.map (CommRingCat.ofHom x.toRingHom) ≫ Pr.κ' h m ≫ D'.p m).app (U h m)).hom (s m))) := by
    intro x
    rw [hc h m (hκU h m).ge (s m)]

    have happ : (Spec.map (CommRingCat.ofHom x.toRingHom)).appLE ⊤ ⊤ le_top =
        (Spec.map (CommRingCat.ofHom x.toRingHom)).appTop :=
      Scheme.Hom.appLE_eq_app _

    have M : (Pr.κ' h m ≫ D'.p m).appLE (U h m) ⊤ (hκU h m).ge ≫ (Scheme.ΓSpecIso _).hom ≫
          CommRingCat.ofHom x.toRingHom =
        (Spec.map (CommRingCat.ofHom x.toRingHom) ≫ Pr.κ' h m ≫ D'.p m).appLE (U h m) ⊤ (hpre x) ≫
          (Scheme.ΓSpecIso (CommRingCat.of B)).hom := by
      rw [← Scheme.ΓSpecIso_naturality, ← happ]
      exact Scheme.Hom.appLE_comp_appLE_assoc _ _ _ _ _ _ _ _
    have e := congrArg (fun φ => φ.hom (s m)) M
    simp only [Scheme.Hom.appLE, Scheme.Hom.comp_app, CommRingCat.hom_comp, CommRingCat.hom_ofHom,
      RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom, AlgHom.toRingHom_eq_coe] at e ⊢
    exact e

  have hval : ∀ (f f' : Spec (CommRingCat.of B) ⟶ D'.Y m)
      (hf : (⊤ : (Spec (CommRingCat.of B)).Opens) ≤ f ⁻¹ᵁ (U h m)) (hf' : (⊤ : (Spec (CommRingCat.of B)).Opens) ≤ f' ⁻¹ᵁ (U h m)),
      f = f' →
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((Spec (CommRingCat.of B)).presheaf.map (homOfLE hf).op ((f.app (U h m)).hom (s m))) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((Spec (CommRingCat.of B)).presheaf.map (homOfLE hf').op ((f'.app (U h m)).hom (s m))) := by
    rintro f f' hf hf' rfl; rfl
  rw [← hsc m, F3 xbar, F3 xbar']
  exact hval _ _ (hpre xbar) (hpre xbar') F2

end S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_nrFunctions_inv_of_sections
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_nrFunctions_inv_of_sections (solution)
