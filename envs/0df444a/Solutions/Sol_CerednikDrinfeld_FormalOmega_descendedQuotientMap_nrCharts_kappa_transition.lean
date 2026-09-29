-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.descendedQuotientMap_nrCharts_kappa_transition
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/3c26f56f-2fc5-55b7-a1d8-019fd8b794c0

import Definitions.Def_CerednikDrinfeld_FormalQuotientDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordTower
import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum
import Definitions.Def_CerednikDrinfeld_MumfordNrPresentation

import Theorems.Thm_CerednikDrinfeld_FormalOmega_chartERing_existsUnique_isPushout_baseChange
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_nrCharts_kappa_transition
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

private theorem spec_quotientMap_factor_comm {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    {J₁ J₂ : Ideal R} {I₁ I₂ : Ideal S} (hJ : J₁ ≤ J₂) (hI : I₁ ≤ I₂) (h₁ : J₁ ≤ I₁.comap f) (h₂ : J₂ ≤ I₂.comap f) :
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap I₂ f h₂)) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hJ)) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hI)) ≫ Spec.map (CommRingCat.ofHom (Ideal.quotientMap I₁ f h₁)) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun y => ?_)
  simp only [RingHom.comp_apply, Ideal.quotientMap_mk, Ideal.Quotient.factor_mk]

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
    :
    ∀ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ),
      Pr.κ' h n ≫ Pr.xt' n = Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr
            (pow_dvd_pow (algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) (Nat.le_succ (n + 1)))))) ≫ Pr.κ' h (n + 1) := by
  classical
  haveI := hdvr
  let A : Type := chartERing Onr (algebraMap 𝒪 Onr π) r
  let I : ℕ → Ideal A := fun m => Ideal.span {(algebraMap Onr A (algebraMap 𝒪 Onr π)) ^ (m + 1)}
  have hle : ∀ n : ℕ, I (n + 1) ≤ I n := fun n =>
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow (algebraMap Onr A (algebraMap 𝒪 Onr π)) (Nat.le_succ (n + 1)))
  obtain ⟨φ, hφalg, hφξ, hφη, -, -⟩ := CerednikDrinfeld.FormalOmega.chartERing.existsUnique_isPushout_baseChange 𝒪 π r Onr
  intro h n

  letI algAn : Algebra 𝒪 (A ⧸ I n) := ((algebraMap Onr (A ⧸ I n)).comp (algebraMap 𝒪 Onr)).toAlgebra
  haveI : IsScalarTower 𝒪 Onr (A ⧸ I n) := IsScalarTower.of_algebraMap_eq (R := 𝒪) (S := Onr) (A := A ⧸ I n) (fun _ => rfl)
  have hπA : algebraMap 𝒪 (A ⧸ I n) π = Ideal.Quotient.mk (I n) (algebraMap Onr A (algebraMap 𝒪 Onr π)) := by
    rw [Ideal.Quotient.mk_algebraMap]; rfl
  have hAn : (algebraMap 𝒪 (A ⧸ I n) π) ^ (n + 1) = 0 := by
    rw [hπA, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hAn' : (algebraMap 𝒪 (A ⧸ I n) π) ^ (n + 1 + 1) = 0 := by rw [pow_succ, hAn, zero_mul]

  let x𝒪 : chartERing 𝒪 π r →ₐ[𝒪] (A ⧸ I n) :=
    { toRingHom := (Ideal.Quotient.mk (I n)).comp φ
      commutes' := fun c => by
        show Ideal.Quotient.mk (I n) (φ (algebraMap 𝒪 (chartERing 𝒪 π r) c)) = algebraMap 𝒪 (A ⧸ I n) c
        have hc := congrArg (fun ψ : 𝒪 →+* A => ψ c) hφalg
        simp only [RingHom.comp_apply] at hc
        rw [hc, Ideal.Quotient.mk_algebraMap]
        rfl }
  have hxξ : x𝒪 (chartERing.ξ 𝒪 π r) = (AlgHom.id Onr (A ⧸ I n)) (Ideal.Quotient.mk (I n) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r)) := by
    show Ideal.Quotient.mk (I n) (φ (chartERing.ξ 𝒪 π r)) = _
    rw [hφξ]; rfl
  have hxη : x𝒪 (chartERing.η 𝒪 π r) = (AlgHom.id Onr (A ⧸ I n)) (Ideal.Quotient.mk (I n) (chartERing.η Onr (algebraMap 𝒪 Onr π) r)) := by
    show Ideal.Quotient.mk (I n) (φ (chartERing.η 𝒪 π r)) = _
    rw [hφη]; rfl

  have hnil : IsNilpotent (algebraMap 𝒪 (A ⧸ I n) π) := ⟨n + 1, hAn⟩
  obtain ⟨d, hd₁, hd₂, hd₃⟩ := CerednikDrinfeld.FormalOmega.exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent
    π hπ r hres g₁ hg₁ (A ⧸ I n) hnil x𝒪
  let P : DeligneDatum (K := K₀) π (A ⧸ I n) := DeligneDatum.pullback π (A ⧸ I n) h⁻¹ d
  have hP : DeligneDatum.IsPullback (K := K₀) (π := π) (A ⧸ I n) h⁻¹ d P := DeligneDatum.isPullback_pullback _ _ _ _

  have hL : Pr.κ' h n ≫ Pr.qX n ≫ pr₁ n = DM.q n (A ⧸ I n) hAn P := by
    have := Pr.κ'_pr₁ h n (A ⧸ I n) hAn (AlgHom.id Onr (A ⧸ I n)) d P
      ⟨by rw [← hxξ]; exact hd₁, by rw [← hxη]; exact hd₂, hd₃⟩ hP
    have hid : Spec.map (CommRingCat.ofHom (AlgHom.id Onr (A ⧸ I n)).toRingHom) = 𝟙 _ := by
      rw [show (AlgHom.id Onr (A ⧸ I n)).toRingHom = RingHom.id _ from rfl, CommRingCat.ofHom_id]
      exact Spec.map_id _
    rw [hid, Category.id_comp] at this
    exact this

  have hfξ : (Ideal.Quotient.factorₐ Onr (hle n)) (Ideal.Quotient.mk (I (n + 1)) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r)) =
      (AlgHom.id Onr (A ⧸ I n)) (Ideal.Quotient.mk (I n) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r)) :=
    Ideal.Quotient.factor_mk (hle n) _
  have hfη : (Ideal.Quotient.factorₐ Onr (hle n)) (Ideal.Quotient.mk (I (n + 1)) (chartERing.η Onr (algebraMap 𝒪 Onr π) r)) =
      (AlgHom.id Onr (A ⧸ I n)) (Ideal.Quotient.mk (I n) (chartERing.η Onr (algebraMap 𝒪 Onr π) r)) :=
    Ideal.Quotient.factor_mk (hle n) _
  have hR : Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (hle n))) ≫ Pr.κ' h (n + 1) ≫ Pr.qX (n + 1) ≫ pr₁ (n + 1) =
      DM.q (n + 1) (A ⧸ I n) hAn' P := by
    exact Pr.κ'_pr₁ h (n + 1) (A ⧸ I n) hAn' (Ideal.Quotient.factorₐ Onr (hle n)) d P
      ⟨by rw [hfξ, ← hxξ]; exact hd₁, by rw [hfη, ← hxη]; exact hd₂, hd₃⟩ hP

  apply (Pr.hq (n + 1)).hom_ext
  ·
    rw [Category.assoc, Pr.hq_xt n, Category.assoc]
    apply (hX (n + 1)).hom_ext
    ·
      simp only [Category.assoc]
      rw [hxt₁ n, reassoc_of% hL, ← DM.q_zt n (A ⧸ I n) hAn hAn' P, hR]
    ·
      simp only [Category.assoc]
      rw [hxt₂ n, reassoc_of% (Pr.κ'_pr₂ h n), Pr.κ'_pr₂ h (n + 1)]
      exact spec_quotientMap_factor_comm _ _ _ _ _
  ·
    rw [Category.assoc, (Pr.hcart' n).w, reassoc_of% (Pr.κ'_xb' h n), Category.assoc, Pr.κ'_xb' h (n + 1)]
    exact spec_quotientMap_factor_comm _ _ _ _ _

end S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_nrCharts_kappa_transition
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_descendedQuotientMap_nrCharts_kappa_transition (solution)
