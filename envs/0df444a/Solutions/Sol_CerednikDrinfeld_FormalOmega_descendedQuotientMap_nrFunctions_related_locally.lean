-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.descendedQuotientMap_nrFunctions_related_locally
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/71698e4c-6d07-5fd4-b45d-ffed3ac8a40b

import Definitions.Def_CerednikDrinfeld_FormalQuotientDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordTower
import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum
import Definitions.Def_CerednikDrinfeld_MumfordNrPresentation
import Theorems.Thm_CerednikDrinfeld_FormalOmega_Omega_action_scalarGL
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_nrFunctions_related_locally

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
p2m_open "CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_nrFunctions_related_locally.CerednikDrinfeld CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_nrFunctions_related_locally.CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "scalar_eq_scalarGL tree BruhatTits.scalar_eq_scalarGL"
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "stdFullLattice stdBasisVec DeligneDatum.pullback DeligneDatum.isPullback_pullback Omega DeligneDatum.map_pullback Omega.action FullLattice.act actBaseChange DeligneDatum DeligneDatum.ext' DeligneDatum.IsPullback OmegaNr.IsTwistedAct AlgFunctor AlgFunctor.prod AlgFunctor.corep chartERing chartERing.ξ chartERing.η MumfordTower MumfordTower.NrPresentation Omega.action_scalarGL"
namespace E2aAux
p2m_open "CerednikDrinfeld.FormalOmega CerednikDrinfeld"

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable (B : Type) [CommRing B] [Algebra 𝒪 B]

theorem isPullback_iff (g : GL (Fin 2) K) (d d' : DeligneDatum (K := K) π B) :
    DeligneDatum.IsPullback (K := K) π B g d d' ↔ d' = DeligneDatum.pullback π B g d := by
  constructor
  · intro h
    apply DeligneDatum.ext'
    funext M
    exact h M
  · rintro rfl
    exact DeligneDatum.isPullback_pullback π B g d

theorem act_eq (g : GL (Fin 2) K) (d : DeligneDatum (K := K) π B) :
    (Omega.action K π).act B g d = DeligneDatum.pullback π B g⁻¹ d := rfl

theorem pullback_inv_eq_of_mk_eq (g g' : GL (Fin 2) K) (h : Matrix.ProjGenLinGroup.mk g = Matrix.ProjGenLinGroup.mk g')
    (d : DeligneDatum (K := K) π B) :
    DeligneDatum.pullback π B g'⁻¹ d = DeligneDatum.pullback π B g⁻¹ d := by
  have h' : (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) K))) g = (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) K))) g' := h
  rw [QuotientGroup.mk'_eq_mk'] at h'
  obtain ⟨z, hz, rfl⟩ := h'
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  obtain ⟨c, rfl⟩ := hz
  rw [BruhatTits.scalar_eq_scalarGL, ← act_eq, ← act_eq, (Omega.action K π).act_mul B g (scalarGL c) d]
  change (Omega.action K π).act B g ((Omega.action K π).act B (scalarGL c) d) = _
  rw [Omega.action_scalarGL π B c d]

end CerednikDrinfeld.FormalOmega.E2aAux

open CerednikDrinfeld.FormalOmega.E2aAux

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
    (h : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (m : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra Onr B] [IsScalarTower 𝒪 Onr B]
    (hB : (algebraMap 𝒪 B π) ^ (m + 1) = 0)
    (xbar xbar' : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) →ₐ[Onr] B) (d d' P P' : DeligneDatum (K := K₀) π B)
    (hd : (d.line (stdFullLattice K₀) =
              Submodule.span B {(xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
            d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
              (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
                (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
            d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)))
    (hd' : (d'.line (stdFullLattice K₀) =
              Submodule.span B {(xbar' (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
            d'.line (FullLattice.act g₁ (stdFullLattice K₀)) =
              (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (xbar' (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (m + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
                (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
            d'.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)))
    (hP : DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d P) (hP' : DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d' P')
    (g : G₂)
    (hpt : Spec.map (CommRingCat.ofHom xbar.toRingHom) ≫ Pr.κ' h m = (Spec.map (CommRingCat.ofHom xbar'.toRingHom) ≫ Pr.κ' h m) ≫ (Pr.a' m g).hom)
    :
    ∃ (ι : Type) (_ : Finite ι) (f : ι → B), Ideal.span (Set.range f) = ⊤ ∧
      ∀ (i : ι) (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] [IsLocalization.Away (f i) C],
        ∃ γ ∈ Γ', DeligneDatum.IsPullback (K := K₀) (π := π) C (σ γ)⁻¹
          ((Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B C) P) ((Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B C) P') := by
  classical
  haveI := hdvr
  rcases subsingleton_or_nontrivial B with hsub | hnon
  ·
    refine ⟨PEmpty, inferInstance, fun i => PEmpty.elim i, ?_, fun i => PEmpty.elim i⟩
    haveI : Subsingleton (Ideal B) := Unique.instSubsingleton
    exact Subsingleton.elim _ _

  have hgE : g ∈ ((Γ'.subgroupOf Γ).map θ) := by
    apply Pr.parity m g h h
    obtain ⟨p⟩ := (inferInstance : Nonempty (PrimeSpectrum B))
    refine ⟨(Spec.map (CommRingCat.ofHom xbar.toRingHom) ≫ Pr.κ' h m).base p,
      ⟨(Spec.map (CommRingCat.ofHom xbar.toRingHom)).base p, ?_⟩,
      ⟨(Spec.map (CommRingCat.ofHom xbar'.toRingHom)).base p, ?_⟩⟩
    · rfl
    · rw [hpt]
      rfl
  obtain ⟨γ₀, hγ₀, hθ⟩ := Subgroup.mem_map.mp hgE
  have hγ₀' : (γ₀ : G) ∈ Γ' := Subgroup.mem_subgroupOf.mp hγ₀

  have h1 : Spec.map (CommRingCat.ofHom xbar.toRingHom) ≫ Pr.κ' h m ≫ Pr.qX m ≫ pr₁ m = DM.q m B hB P :=
    Pr.κ'_pr₁ h m B hB xbar d P hd hP
  have h2 : Spec.map (CommRingCat.ofHom xbar'.toRingHom) ≫ Pr.κ' h m ≫ Pr.qX m ≫ pr₁ m = DM.q m B hB P' :=
    Pr.κ'_pr₁ h m B hB xbar' d' P' hd' hP'
  have hP'' : DeligneDatum.IsPullback (K := K₀) (π := π) B (σ (γ₀ : G))⁻¹ P'
      (DeligneDatum.pullback π B (σ (γ₀ : G))⁻¹ P') :=
    DeligneDatum.isPullback_pullback π B _ P'
  have h3 : ((Spec.map (CommRingCat.ofHom xbar'.toRingHom) ≫ Pr.κ' h m ≫ Pr.qX m) ≫ (a m (θ γ₀)).hom) ≫ pr₁ m =
      DM.q m B hB (DeligneDatum.pullback π B (σ (γ₀ : G))⁻¹ P') :=
    ha_pr₁ m γ₀ B hB P' _ hP'' _ (by simpa only [Category.assoc] using h2)
  have hq_eq : DM.q m B hB P = DM.q m B hB (DeligneDatum.pullback π B (σ (γ₀ : G))⁻¹ P') := by
    rw [← h1, ← h3, hθ]
    calc Spec.map (CommRingCat.ofHom xbar.toRingHom) ≫ Pr.κ' h m ≫ Pr.qX m ≫ pr₁ m
        = (Spec.map (CommRingCat.ofHom xbar.toRingHom) ≫ Pr.κ' h m) ≫ Pr.qX m ≫ pr₁ m := by
          simp only [Category.assoc]
      _ = ((Spec.map (CommRingCat.ofHom xbar'.toRingHom) ≫ Pr.κ' h m) ≫ (Pr.a' m g).hom) ≫ Pr.qX m ≫ pr₁ m := by rw [hpt]
      _ = (Spec.map (CommRingCat.ofHom xbar'.toRingHom) ≫ Pr.κ' h m) ≫ ((Pr.a' m g).hom ≫ Pr.qX m) ≫ pr₁ m := by
          simp only [Category.assoc]
      _ = (Spec.map (CommRingCat.ofHom xbar'.toRingHom) ≫ Pr.κ' h m) ≫ (Pr.qX m ≫ (a m g).hom) ≫ pr₁ m := by
          rw [Pr.hq_a m g]
      _ = ((Spec.map (CommRingCat.ofHom xbar'.toRingHom) ≫ Pr.κ' h m ≫ Pr.qX m) ≫ (a m g).hom) ≫ pr₁ m := by
          simp only [Category.assoc]

  obtain ⟨ι, hι, f, hf, hloc⟩ := DM.q_zarFib m B hB P _ hq_eq
  refine ⟨ι, hι, f, hf, ?_⟩
  intro i C _ _ _ _ _
  obtain ⟨n, hnN, hnpb⟩ := hloc i C
  obtain ⟨δ, hδ, hρδ⟩ := Subgroup.mem_map.mp (hNle hnN)
  rw [hρ] at hρδ
  refine ⟨(γ₀ : G)⁻¹ * δ, Γ'.mul_mem (Γ'.inv_mem hγ₀') hδ, ?_⟩
  have e1 : (Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B C) (DeligneDatum.pullback π B (σ (γ₀ : G))⁻¹ P') =
      DeligneDatum.pullback π C n⁻¹ ((Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B C) P) :=
    (isPullback_iff π C n⁻¹ _ _).mp hnpb
  have e2 : (Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B C) (DeligneDatum.pullback π B (σ (γ₀ : G))⁻¹ P') =
      DeligneDatum.pullback π C (σ (γ₀ : G))⁻¹ ((Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B C) P') :=
    DeligneDatum.map_pullback π (IsScalarTower.toAlgHom 𝒪 B C) _ P'
  have e3 : DeligneDatum.pullback π C n⁻¹ ((Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B C) P) =
      DeligneDatum.pullback π C (σ δ)⁻¹ ((Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B C) P) :=
    pullback_inv_eq_of_mk_eq π C (σ δ) n hρδ _
  have key : (Omega.action K₀ π).act C (σ (γ₀ : G)) ((Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B C) P') =
      (Omega.action K₀ π).act C (σ δ) ((Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B C) P) := by
    rw [act_eq, act_eq, ← e2, e1, e3]
  have hfin : (Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B C) P' =
      (Omega.action K₀ π).act C ((σ (γ₀ : G))⁻¹ * σ δ) ((Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B C) P) := by
    rw [(Omega.action K₀ π).act_mul, ← key, ← (Omega.action K₀ π).act_mul, inv_mul_cancel, (Omega.action K₀ π).act_one]
  rw [isPullback_iff, map_mul, map_inv, ← act_eq]
  exact hfin

end S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_nrFunctions_related_locally
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_nrFunctions_related_locally (solution)
