-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.descendedQuotientMap_nrFunctions_overlap_agreement
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/0f6b9de7-4912-5401-ae6f-48e8cb8bc622

import Definitions.Def_CerednikDrinfeld_FormalQuotientDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordTower
import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum
import Definitions.Def_CerednikDrinfeld_MumfordNrPresentation
import Theorems.Thm_CerednikDrinfeld_FormalOmega_chartERing_existsUnique_isPushout_baseChange
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_inEdgeChart_of_line_eq
import Theorems.Thm_CerednikDrinfeld_FormalOmega_descendedQuotientMap_nrFunctions_related_locally
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_nrFunctions_overlap_agreement
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega
set_option maxHeartbeats 8000000 in
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
    (hinv : ∀ (m : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra Onr B] [IsScalarTower 𝒪 Onr B],
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
                xbar (fam m) = xbar' (fam m))
    (m : ℕ) (g : G₂) (B : Type) [CommRing B] (x x' : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) →+* B)
    (hpt : Spec.map (CommRingCat.ofHom x) ≫ Pr.κ' h m = (Spec.map (CommRingCat.ofHom x') ≫ Pr.κ' h m) ≫ (Pr.a' m g).hom)
    :
    x (fam m) = x' (fam m) := by
  classical

  have hOnr : x.comp (algebraMap Onr ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)})) = x'.comp (algebraMap Onr ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)})) := by
    have e := congrArg (fun φ => φ ≫ Pr.xb' m) hpt
    simp only [Category.assoc] at e
    rw [Pr.ha'_over, Pr.κ'_xb', ← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at e
    apply RingHom.ext
    intro o
    have e' := congrArg (fun φ => φ.hom (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 Onr π) ^ (m + 1)}) o)) e
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, Ideal.quotientMap_mk] at e'
    exact e'
  letI algOnrB : Algebra Onr B := (x.comp (algebraMap Onr ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}))).toAlgebra
  letI algOB : Algebra 𝒪 B := ((x.comp (algebraMap Onr ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}))).comp (algebraMap 𝒪 Onr)).toAlgebra
  haveI : IsScalarTower 𝒪 Onr B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let xbar : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) →ₐ[Onr] B := { toRingHom := x, commutes' := fun _ => rfl }
  let xbar' : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) →ₐ[Onr] B :=
    { toRingHom := x', commutes' := fun o => (RingHom.congr_fun hOnr o).symm.trans rfl }
  have hπA : (algebraMap Onr ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (algebraMap 𝒪 Onr π)) ^ (m + 1) = 0 := by
    have : algebraMap Onr ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (algebraMap 𝒪 Onr π) =
        Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) := rfl
    rw [this]
    exact ((map_pow _ _ _).symm).trans (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _))
  have hB : (algebraMap 𝒪 B π) ^ (m + 1) = 0 := by
    change (x (algebraMap Onr _ (algebraMap 𝒪 Onr π))) ^ (m + 1) = 0
    rw [← map_pow, hπA, map_zero]
  have hBnil : IsNilpotent (algebraMap 𝒪 B π) := ⟨m + 1, hB⟩
  haveI : IsDiscreteValuationRing 𝒪 := hdvr

  obtain ⟨φ, hφcomp, hφξ, hφη, -, -⟩ :=
    CerednikDrinfeld.FormalOmega.chartERing.existsUnique_isPushout_baseChange 𝒪 π r Onr
  have hφalg : ∀ o : 𝒪, φ (algebraMap 𝒪 (chartERing 𝒪 π r) o) =
      algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr o) := fun o => RingHom.congr_fun hφcomp o

  have chartData : ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra Onr C] [IsScalarTower 𝒪 Onr C]
      (y : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) →ₐ[Onr] C), IsNilpotent (algebraMap 𝒪 C π) →
      ∃ d : DeligneDatum (K := K₀) π C,
        (d.line (stdFullLattice K₀) =
            Submodule.span C {(y (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : C) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
          d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
            (Submodule.span C {(1 : C) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (y (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
              (actBaseChange C g₁ (stdFullLattice K₀)).toLinearMap ∧
          d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) := by
    intro C _ _ _ _ y hC
    let y₀ : chartERing 𝒪 π r →ₐ[𝒪] C :=
      { toRingHom := y.toRingHom.comp ((Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)})).comp φ)
        commutes' := fun o => by
          change y (Ideal.Quotient.mk _ (φ (algebraMap 𝒪 (chartERing 𝒪 π r) o))) = algebraMap 𝒪 C o
          rw [hφalg, show Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr o))
            = algebraMap Onr _ (algebraMap 𝒪 Onr o) from rfl, AlgHom.commutes, ← IsScalarTower.algebraMap_apply] }
    obtain ⟨d, h1, h2, h3⟩ := CerednikDrinfeld.FormalOmega.exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent
      π hπ r hres g₁ hg₁ C hC y₀
    have hξ : y₀ (chartERing.ξ 𝒪 π r) = y (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r)) := by
      change y (Ideal.Quotient.mk _ (φ (chartERing.ξ 𝒪 π r))) = _; rw [hφξ]
    have hη : y₀ (chartERing.η 𝒪 π r) = y (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r)) := by
      change y (Ideal.Quotient.mk _ (φ (chartERing.η 𝒪 π r))) = _; rw [hφη]
    refine ⟨d, ⟨?_, ?_, h3⟩⟩
    · rw [h1, hξ]
    · rw [h2, hη]
  obtain ⟨d, hd⟩ := chartData B xbar hBnil
  obtain ⟨d', hd'⟩ := chartData B xbar' hBnil
  let P := DeligneDatum.pullback π B h⁻¹ d
  let P' := DeligneDatum.pullback π B h⁻¹ d'
  have hP : DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d P := DeligneDatum.isPullback_pullback π B h⁻¹ d
  have hP' : DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d' P' := DeligneDatum.isPullback_pullback π B h⁻¹ d'

  obtain ⟨ι, hι, fcov, hspan, hloc⟩ := CerednikDrinfeld.FormalOmega.descendedQuotientMap_nrFunctions_related_locally 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet G σ Γ hcent hodd Γ' hΓ' ρ hρ hdisc hcocpt g₁ hg₁ N hNle hNnorm hNidx DM X xb xt G₂ a pr₁ pr₂ θ Fr₂ hcart hproper hflat haff ha_over ha_xt hX hxb hxt₁ hxt₂ hθsurj hθker hFr₂ ha_pr₂ ha_pr₁ DQ q hqdef hqover hqnat hqyt hqinv Pr D' rY hrY hrY_p hrY_yt h m B hB xbar xbar' d d' P P' hd hd' hP hP' g hpt

  have hlocEq : ∀ i : ι, algebraMap B (Localization.Away (fcov i)) (x (fam m)) =
      algebraMap B (Localization.Away (fcov i)) (x' (fam m)) := by
    intro i
    let C := Localization.Away (fcov i)
    haveI : IsScalarTower 𝒪 Onr C := IsScalarTower.of_algebraMap_eq (fun o => by
      rw [IsScalarTower.algebraMap_apply 𝒪 B C, IsScalarTower.algebraMap_apply Onr B C, IsScalarTower.algebraMap_apply 𝒪 Onr B])
    obtain ⟨γ, hγ, hrel⟩ := hloc i C
    let fC : B →ₐ[𝒪] C := IsScalarTower.toAlgHom 𝒪 B C
    have hCnil : IsNilpotent (algebraMap 𝒪 C π) := ⟨m + 1, by
      rw [IsScalarTower.algebraMap_apply 𝒪 B C, ← map_pow, hB, map_zero]⟩
    let xC : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) →ₐ[Onr] C := (IsScalarTower.toAlgHom Onr B C).comp xbar
    let xC' : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) →ₐ[Onr] C := (IsScalarTower.toAlgHom Onr B C).comp xbar'
    obtain ⟨dC, hdC⟩ := chartData C xC hCnil
    obtain ⟨dC', hdC'⟩ := chartData C xC' hCnil

    have lineBC_span : ∀ (M : FullLattice 𝒪 K₀) (v : latticeBaseChange 𝒪 K₀ B M),
        lineBaseChange fC M (Submodule.span B {v}) = Submodule.span C {LinearMap.rTensor (↥M.1) fC.toLinearMap v} := by
      intro M v
      apply le_antisymm
      · rw [lineBaseChange]
        apply Submodule.span_le.2
        rintro _ ⟨n, hn, rfl⟩
        obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hn
        rw [rTensor_smul_left fC M b v]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      · apply Submodule.span_le.2
        rintro _ rfl
        exact Submodule.subset_span ⟨v, Submodule.mem_span_singleton_self _, rfl⟩
    have lineBC_map : ∀ (M : FullLattice 𝒪 K₀) (gg : Matrix.GeneralLinearGroup (Fin 2) K₀) (w : latticeBaseChange 𝒪 K₀ B M),
        lineBaseChange fC (FullLattice.act gg M) ((Submodule.span B {w}).map (actBaseChange B gg M).toLinearMap) =
          (Submodule.span C {LinearMap.rTensor (↥M.1) fC.toLinearMap w}).map (actBaseChange C gg M).toLinearMap := by
      intro M gg w
      have hw := rTensor_actBaseChange fC gg M w
      rw [Submodule.map_span, Submodule.map_span, Set.image_singleton, Set.image_singleton, lineBC_span]
      simp only [LinearEquiv.coe_coe] at hw ⊢
      rw [hw]
    have hmapd : (Omega K₀ π).map fC d = dC := by
      obtain ⟨h1, h2, h3⟩ := hdC
      obtain ⟨k1, k2, -⟩ := hd
      symm
      apply (CerednikDrinfeld.FormalOmega.DeligneDatum.eq_of_inEdgeChart_of_line_eq hπ dC ((Omega K₀ π).map fC d) _ _ h3 ?_ ?_).symm
      · show lineBaseChange fC _ (d.line _) = dC.line _
        rw [k1, h1, lineBC_span, map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
          AlgHom.toLinearMap_apply, map_one]
        rfl
      · show lineBaseChange fC _ (d.line _) = dC.line _
        rw [k2, h2, lineBC_map, map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
          AlgHom.toLinearMap_apply, map_one]
        rfl
    have hmapd' : (Omega K₀ π).map fC d' = dC' := by
      obtain ⟨h1, h2, h3⟩ := hdC'
      obtain ⟨k1, k2, -⟩ := hd'
      symm
      apply (CerednikDrinfeld.FormalOmega.DeligneDatum.eq_of_inEdgeChart_of_line_eq hπ dC' ((Omega K₀ π).map fC d') _ _ h3 ?_ ?_).symm
      · show lineBaseChange fC _ (d'.line _) = dC'.line _
        rw [k1, h1, lineBC_span, map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
          AlgHom.toLinearMap_apply, map_one]
        rfl
      · show lineBaseChange fC _ (d'.line _) = dC'.line _
        rw [k2, h2, lineBC_map, map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
          AlgHom.toLinearMap_apply, map_one]
        rfl

    have hPC : DeligneDatum.IsPullback (K := K₀) (π := π) C h⁻¹ dC ((Omega K₀ π).map fC P) := by
      rw [← hmapd]
      show DeligneDatum.IsPullback (K := K₀) (π := π) C h⁻¹ (d.map π fC) ((DeligneDatum.pullback π B h⁻¹ d).map π fC)
      rw [DeligneDatum.map_pullback]
      exact DeligneDatum.isPullback_pullback π C h⁻¹ _
    have hPC' : DeligneDatum.IsPullback (K := K₀) (π := π) C h⁻¹ dC' ((Omega K₀ π).map fC P') := by
      rw [← hmapd']
      show DeligneDatum.IsPullback (K := K₀) (π := π) C h⁻¹ (d'.map π fC) ((DeligneDatum.pullback π B h⁻¹ d').map π fC)
      rw [DeligneDatum.map_pullback]
      exact DeligneDatum.isPullback_pullback π C h⁻¹ _
    have := hinv m C hCnil xC xC' dC dC' _ _ hdC hdC' hPC hPC' ⟨γ, hγ, hrel⟩
    exact this

  haveI := hι
  exact Module.eq_of_isLocalized_span (Set.range fcov) hspan (fun r => Localization.Away (r : B))
    (fun r => Algebra.linearMap B (Localization.Away (r : B))) (x (fam m)) (x' (fam m))
    (fun r => by
      obtain ⟨i, hi⟩ := r.2
      have := hlocEq i
      rw [hi] at this
      exact this)

end S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_nrFunctions_overlap_agreement
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_nrFunctions_overlap_agreement (solution)
