-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.MumfordTower.nonempty_nrPresentation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/8a785706-850e-51ef-8d88-47c8009e7acd

import Definitions.Def_CerednikDrinfeld_FormalQuotientDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordTower
import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum
import Definitions.Def_CerednikDrinfeld_MumfordNrPresentation
import Theorems.Thm_CerednikDrinfeld_FormalOmega_chartERing_existsUnique_isPushout_quotient_baseChange
import Theorems.Thm_AlgebraicGeometry_exists_tower_baseChange_of_isPullback
import Theorems.Thm_CerednikDrinfeld_FormalOmega_chartERing_existsUnique_isPushout_baseChange
import Theorems.Thm_CerednikDrinfeld_UnramQuad_bijective_lift_prod_equalizer_frobenius_sq_tensor
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_inEdgeChart_of_line_eq
import Theorems.Thm_CerednikDrinfeld_UnramQuad_free_finrank_two_equalizer_frobenius_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_nonempty_nrPresentation
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

namespace D1Body

theorem lineBaseChange_span_singleton {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
    (M : FullLattice 𝒪 K) (v : latticeBaseChange 𝒪 K B M) :
    lineBaseChange f M (Submodule.span B {v}) = Submodule.span B' {LinearMap.rTensor (↥M.1) f.toLinearMap v} := by
  apply le_antisymm
  · rw [lineBaseChange, Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [rTensor_smul_left]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [lineBaseChange]
    exact Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨v, Submodule.mem_span_singleton_self v, rfl⟩)

theorem map_eq_of_chartLines {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K]
    [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π) (g₁ : Matrix.GeneralLinearGroup (Fin 2) K)
    {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B') (a b : B)
    (d : DeligneDatum (K := K) π B) (d' : DeligneDatum (K := K) π B')
    (hd₁ : d.line (stdFullLattice K) = Submodule.span B {a ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K 1})
    (hd₂ : d.line (FullLattice.act g₁ (stdFullLattice K)) =
      (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K 0 + b ⊗ₜ[𝒪] stdBasisVec K 1}).map
        (actBaseChange B g₁ (stdFullLattice K)).toLinearMap)
    (hd'₁ : d'.line (stdFullLattice K) = Submodule.span B' {f a ⊗ₜ[𝒪] stdBasisVec K 0 + (1 : B') ⊗ₜ[𝒪] stdBasisVec K 1})
    (hd'₂ : d'.line (FullLattice.act g₁ (stdFullLattice K)) =
      (Submodule.span B' {(1 : B') ⊗ₜ[𝒪] stdBasisVec K 0 + f b ⊗ₜ[𝒪] stdBasisVec K 1}).map
        (actBaseChange B' g₁ (stdFullLattice K)).toLinearMap)
    (hd'₃ : d'.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K)) (stdFullLattice K)) :
    DeligneDatum.map π f d = d' := by
  refine CerednikDrinfeld.FormalOmega.DeligneDatum.eq_of_inEdgeChart_of_line_eq hπ d' _
    (FullLattice.act g₁ (stdFullLattice K)) (stdFullLattice K) hd'₃ ?_ ?_
  · show lineBaseChange f _ (d.line (stdFullLattice K)) = d'.line (stdFullLattice K)
    rw [hd₁, hd'₁, lineBaseChange_span_singleton, map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
      AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, map_one]
  · show lineBaseChange f _ (d.line (FullLattice.act g₁ (stdFullLattice K))) = d'.line (FullLattice.act g₁ (stdFullLattice K))
    rw [hd₂, hd'₂, Submodule.map_span, Set.image_singleton, lineBaseChange_span_singleton, Submodule.map_span,
      Set.image_singleton, LinearEquiv.coe_coe, LinearEquiv.coe_coe, rTensor_actBaseChange, map_add, LinearMap.rTensor_tmul,
      LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, map_one]

set_option maxHeartbeats 6400000 in

theorem chartData

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
    (n : ℕ) (X'n : Scheme.{0}) (xb'n : X'n ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}))) (qXn : X'n ⟶ X n)
    (hqn : IsPullback qXn xb'n (xb n) (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) (algebraMap 𝒪 Onr)
        (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))))
    (h : Matrix.GeneralLinearGroup (Fin 2) K₀) :
    ∃ κ : Spec (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})) ⟶ X'n,
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra Onr B] [IsScalarTower 𝒪 Onr B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
          (xbar : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) →ₐ[Onr] B) (d P : DeligneDatum (K := K₀) π B),
          (d.line (stdFullLattice K₀) =
              Submodule.span B {(xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
            d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
              (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
                (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
            d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
          DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d P →
          Spec.map (CommRingCat.ofHom xbar.toRingHom) ≫ κ ≫ qXn ≫ pr₁ n = DM.q n B hB P) ∧
      κ ≫ qXn ≫ pr₂ n = Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})
          ((algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r)).comp ((AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val.toRingHom))
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))) ∧
      κ ≫ xb'n = Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})
          (algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r))
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))) := by
  classical
  haveI := hdvr

  letI algOA : Algebra 𝒪 (chartERing Onr (algebraMap 𝒪 Onr π) r) := ((algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r)).comp (algebraMap 𝒪 Onr)).toAlgebra
  haveI istOA : IsScalarTower 𝒪 Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hπOnrA : algebraMap 𝒪 ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) π =
      Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) := rfl
  have hπAn : (algebraMap 𝒪 ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) π) ^ (n + 1) = 0 := by
    rw [hπOnrA]
    exact (map_pow (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})) _ (n + 1)).symm.trans
      (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _))
  have hnil : IsNilpotent (algebraMap 𝒪 ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) π) := ⟨n + 1, hπAn⟩

  have hξη : Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r) *
      Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r) = algebraMap 𝒪 ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) π := by
    rw [← map_mul, chartERing.ξ_mul_η, hπOnrA]
  let ptO : (chartE 𝒪 π r).obj ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) :=
    ⟨(Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r),
      Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r)),
     hξη,
     by have h1 := (chartERing.point Onr (algebraMap 𝒪 Onr π) r).2.2.1.map (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})); rwa [map_sub, map_pow, map_one] at h1,
     by have h2 := (chartERing.point Onr (algebraMap 𝒪 Onr π) r).2.2.2.map (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})); rwa [map_sub, map_pow, map_one] at h2⟩
  let xO : chartERing 𝒪 π r →ₐ[𝒪] ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) := chartERing.lift ptO
  have hxOξ : xO (chartERing.ξ 𝒪 π r) = Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r) := chartERing.lift_ξ ptO
  have hxOη : xO (chartERing.η 𝒪 π r) = Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r) := chartERing.lift_η ptO
  obtain ⟨d, hd₁, hd₂, hd₃⟩ := CerednikDrinfeld.FormalOmega.exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent
    (K := K₀) π hπ r hres g₁ hg₁ ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) hnil xO
  rw [hxOξ] at hd₁
  rw [hxOη] at hd₂
  let P : DeligneDatum (K := K₀) π ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) := DeligneDatum.pullback π ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) h⁻¹ d

  let z : Spec (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})) ⟶ DM.Z n := DM.q n ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) hπAn P
  let e : Spec (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})) ⟶ Spec (CommRingCat.of (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})) := Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})
          ((algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r)).comp ((AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val.toRingHom))
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))
  let s : Spec (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})) ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)})) := Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})
          (algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r))
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

  have hz𝒪 : z ≫ DM.zb n ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
      Spec.map (CommRingCat.ofHom (algebraMap 𝒪 ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}))) := DM.q_over n ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) hπAn P
  have he𝒪 : e ≫ Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)))
            (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))) ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
      Spec.map (CommRingCat.ofHom (algebraMap 𝒪 ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}))) := by
    simp only [e, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  have hs𝒪 : s ≫ Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) (algebraMap 𝒪 Onr)
        (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))) ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))) =
      Spec.map (CommRingCat.ofHom (algebraMap 𝒪 ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}))) := by
    simp only [s, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  have wz : z ≫ DM.zb n = e ≫ Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)))
            (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))) := by
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))))]
    simp only [Category.assoc]
    rw [hz𝒪, he𝒪]
  let x : Spec (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})) ⟶ X n := (hX n).lift z e wz
  have hx₁ : x ≫ pr₁ n = z := (hX n).lift_fst z e wz
  have hx₂ : x ≫ pr₂ n = e := (hX n).lift_snd z e wz
  have wx : x ≫ xb n = s ≫ Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) (algebraMap 𝒪 Onr)
        (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))) := by
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))))]
    simp only [Category.assoc]
    rw [hxb n]
    simp only [Category.assoc]
    rw [reassoc_of% hx₁, hz𝒪, hs𝒪]
  refine ⟨hqn.lift x s wx, ?_, ?_, ?_⟩
  ·
    intro B _ _ _ _ hB xbar d' P' hd' hP'
    rw [hqn.lift_fst_assoc, ← Category.assoc (Spec.map _) x, show (Spec.map (CommRingCat.ofHom xbar.toRingHom) ≫ x) ≫ pr₁ n =
      Spec.map (CommRingCat.ofHom xbar.toRingHom) ≫ z by rw [Category.assoc, hx₁]]

    have hnat := DM.q_natural n ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) B hπAn hB (xbar.restrictScalars 𝒪) P
    rw [show Spec.map (CommRingCat.ofHom xbar.toRingHom) = Spec.map (CommRingCat.ofHom (xbar.restrictScalars 𝒪).toRingHom) from rfl, ← hnat]
    congr 1

    have hd'eq : DeligneDatum.map π (xbar.restrictScalars 𝒪) d = d' := by
      refine CerednikDrinfeld.FormalOmega.DeligneDatum.eq_of_inEdgeChart_of_line_eq hπ d' _
        (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀) hd'.2.2 ?_ ?_
      · show lineBaseChange (xbar.restrictScalars 𝒪) _ (d.line (stdFullLattice K₀)) = d'.line (stdFullLattice K₀)
        rw [hd₁, hd'.1, lineBaseChange_span_singleton]
        congr 2
        rw [map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply,
          map_one]
        rfl
      · show lineBaseChange (xbar.restrictScalars 𝒪) _ (d.line (FullLattice.act g₁ (stdFullLattice K₀))) =
          d'.line (FullLattice.act g₁ (stdFullLattice K₀))
        rw [hd₂, hd'.2.1, Submodule.map_span, Set.image_singleton, lineBaseChange_span_singleton, Submodule.map_span,
          Set.image_singleton, LinearEquiv.coe_coe, LinearEquiv.coe_coe, rTensor_actBaseChange]
        congr 3
        rw [map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply,
          map_one]
        rfl
    show DeligneDatum.map π (xbar.restrictScalars 𝒪) (DeligneDatum.pullback π ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) h⁻¹ d) = P'
    rw [DeligneDatum.map_pullback, hd'eq]
    exact (DeligneDatum.ext' (funext fun M => hP' M)).symm
  · rw [hqn.lift_fst_assoc, hx₂]
  · exact hqn.lift_snd x s wx

set_option maxHeartbeats 6400000 in

theorem chart_openImmersion_range

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
    (n : ℕ) (X'n : Scheme.{0}) (xb'n : X'n ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}))) (qXn : X'n ⟶ X n)
    (hqn : IsPullback qXn xb'n (xb n) (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) (algebraMap 𝒪 Onr)
        (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))))

    (W : Scheme.{0}) (w₁ : W ⟶ DM.Z n) (w₂ : W ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)})))
    (hW : IsPullback w₁ w₂ (DM.zb n) (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) (algebraMap 𝒪 Onr)
        (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))))
    (ιp : W ⟶ X'n) [IsOpenImmersion ιp]
    (hι₁ : ιp ≫ qXn ≫ pr₁ n = w₁) (hι₂ : ιp ≫ xb'n = w₂)
    (hι₃ : ιp ≫ qXn ≫ pr₂ n = w₂ ≫ Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) ((AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val.toRingHom)
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))))

    (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (κ : Spec (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})) ⟶ X'n)
    (hκ₁ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra Onr B] [IsScalarTower 𝒪 Onr B] (hB : (algebraMap 𝒪 B π) ^ (n + 1) = 0)
          (xbar : ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) →ₐ[Onr] B) (d P : DeligneDatum (K := K₀) π B),
          (d.line (stdFullLattice K₀) =
              Submodule.span B {(xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
            d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
              (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (xbar (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r))) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
                (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
            d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
          DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d P →
          Spec.map (CommRingCat.ofHom xbar.toRingHom) ≫ κ ≫ qXn ≫ pr₁ n = DM.q n B hB P)
    (hκ₂ : κ ≫ qXn ≫ pr₂ n = Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})
          ((algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r)).comp ((AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val.toRingHom))
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))))
    (hκ₃ : κ ≫ xb'n = Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})
          (algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r))
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))))

    (hA : (algebraMap 𝒪 ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) π) ^ (n + 1) = 0) (d𝒪 P𝒪 : DeligneDatum (K := K₀) π ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))
    (hd𝒪 : (d𝒪.line (stdFullLattice K₀) =
            Submodule.span ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) {((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
          d𝒪.line (FullLattice.act g₁ (stdFullLattice K₀)) =
            (Submodule.span ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) {(1 : ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
              (actBaseChange ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) g₁ (stdFullLattice K₀)).toLinearMap ∧
          d𝒪.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)))
    (hP𝒪 : DeligneDatum.IsPullback (K := K₀) (π := π) ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) h⁻¹ d𝒪 P𝒪) :
    IsOpenImmersion κ ∧ Set.range κ.base = ιp.base '' (w₁.base ⁻¹' Set.range (DM.q n ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) hA P𝒪).base) := by
  classical
  haveI := hdvr
  letI algOA : Algebra 𝒪 (chartERing Onr (algebraMap 𝒪 Onr π) r) := ((algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r)).comp (algebraMap 𝒪 Onr)).toAlgebra
  haveI istOA : IsScalarTower 𝒪 Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

  obtain ⟨φn, hφcomp, hφξ, hφη, hpo, -⟩ :=
    CerednikDrinfeld.FormalOmega.chartERing.existsUnique_isPushout_quotient_baseChange 𝒪 π r n Onr
  have hPB := AlgebraicGeometry.isPullback_SpecMap_of_isPushout _ _ _ _ hpo

  haveI hchOI : IsOpenImmersion (DM.q n ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) hA P𝒪) := DM.chart_isOpenImmersion h n hA d𝒪 P𝒪 hd𝒪 hP𝒪
  have tO : DM.q n ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) hA P𝒪 ≫ DM.zb n = Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) (algebraMap 𝒪 (chartERing 𝒪 π r))
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))) := by
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))), Category.assoc, DM.q_over, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    congr 2

  have wj : (Spec.map (CommRingCat.ofHom φn) ≫ DM.q n ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) hA P𝒪) ≫ DM.zb n =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})
          (algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r))
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))) ≫ Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) (algebraMap 𝒪 Onr)
        (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))) := by
    rw [Category.assoc, tO]; exact hPB.w.symm
  have hj₁ := hW.lift_fst _ _ wj
  have hj₂ := hW.lift_snd _ _ wj
  have hsq : IsPullback (Spec.map (CommRingCat.ofHom φn)) (hW.lift _ _ wj) (DM.q n ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) hA P𝒪) w₁ := by
    refine IsPullback.of_bot ?_ hj₁.symm hW
    rw [hj₂, tO]
    exact hPB.flip
  haveI hjOI : IsOpenImmersion (hW.lift _ _ wj) := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hsq hchOI

  have hπOnrA : algebraMap 𝒪 ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) π = Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) := rfl
  have hπAn : (algebraMap 𝒪 ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) π) ^ (n + 1) = 0 := by
    rw [hπOnrA]
    exact (map_pow (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})) _ (n + 1)).symm.trans
      (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _))
  have hξη : Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r) *
      Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r) = algebraMap 𝒪 ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) π := by
    rw [← map_mul, chartERing.ξ_mul_η, hπOnrA]
  let ptO : (chartE 𝒪 π r).obj ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) :=
    ⟨(Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r),
      Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r)),
     hξη,
     by have h1 := (chartERing.point Onr (algebraMap 𝒪 Onr π) r).2.2.1.map (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})); rwa [map_sub, map_pow, map_one] at h1,
     by have h2 := (chartERing.point Onr (algebraMap 𝒪 Onr π) r).2.2.2.map (Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})); rwa [map_sub, map_pow, map_one] at h2⟩
  obtain ⟨d, hd₁, hd₂, hd₃⟩ := CerednikDrinfeld.FormalOmega.exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent
    (K := K₀) π hπ r hres g₁ hg₁ ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) ⟨n + 1, hπAn⟩ (chartERing.lift ptO)
  have hxOξ : chartERing.lift ptO (chartERing.ξ 𝒪 π r) = Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r) :=
    chartERing.lift_ξ ptO
  have hxOη : chartERing.lift ptO (chartERing.η 𝒪 π r) = Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r) :=
    chartERing.lift_η ptO
  rw [hxOξ] at hd₁
  rw [hxOη] at hd₂

  let φa : ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) →ₐ[𝒪] ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) :=
    { toRingHom := φn
      commutes' := fun a => by
        have := congrArg (fun f : (𝒪 ⧸ Ideal.span {π ^ (n + 1)}) →+* ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) => f (Ideal.Quotient.mk _ a)) hφcomp
        simp only [RingHom.coe_comp, Function.comp_apply] at this
        exact this }
  have hφξ' : φa ((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) (chartERing.ξ 𝒪 π r)) =
      Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.ξ Onr (algebraMap 𝒪 Onr π) r) := hφξ
  have hφη' : φa ((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) (chartERing.η 𝒪 π r)) =
      Ideal.Quotient.mk (Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) (chartERing.η Onr (algebraMap 𝒪 Onr π) r) := hφη
  rw [← hφξ'] at hd₁
  rw [← hφη'] at hd₂
  have hmapd : DeligneDatum.map π φa d𝒪 = d :=
    map_eq_of_chartLines hπ g₁ φa _ _ d𝒪 d hd𝒪.1 hd𝒪.2.1 hd₁ hd₂ hd₃
  rw [hφξ'] at hd₁
  rw [hφη'] at hd₂
  have hPeq : P𝒪 = DeligneDatum.pullback π ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) h⁻¹ d𝒪 := DeligneDatum.ext' (funext fun M => hP𝒪 M)
  have hmapP : (Omega K₀ π).map φa P𝒪 = DeligneDatum.pullback π ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) h⁻¹ d := by
    show DeligneDatum.map π φa P𝒪 = _
    rw [hPeq, DeligneDatum.map_pullback, hmapd]

  have hκ : κ = hW.lift _ _ wj ≫ ιp := by
    apply hqn.hom_ext
    · apply (hX n).hom_ext
      · have h1 := hκ₁ ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) hπAn (AlgHom.id Onr ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})) d (DeligneDatum.pullback π ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) h⁻¹ d) ⟨hd₁, hd₂, hd₃⟩
          (DeligneDatum.isPullback_pullback π ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) h⁻¹ d)
        rw [show Spec.map (CommRingCat.ofHom (AlgHom.id Onr ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)})).toRingHom) = 𝟙 _ from Spec.map_id _, Category.id_comp] at h1
        simp only [Category.assoc]
        rw [h1, hι₁, hj₁, ← hmapP]
        exact DM.q_natural n ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}) hA hπAn φa P𝒪
      · simp only [Category.assoc]
        rw [hκ₂, hι₃, reassoc_of% hj₂, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2
        exact Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
    · simp only [Category.assoc]
      rw [hκ₃, hι₂, hj₂]
  have hrange_j : Set.range (hW.lift _ _ wj).base = w₁.base ⁻¹' Set.range (DM.q n ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) hA P𝒪).base := by
    rw [show hW.lift _ _ wj = hsq.isoPullback.hom ≫ Limits.pullback.snd _ _ from hsq.isoPullback_hom_snd.symm]
    ext y
    simp only [Set.mem_range, Scheme.Hom.comp_apply, Set.mem_preimage]
    constructor
    · rintro ⟨x, rfl⟩
      have : (Limits.pullback.snd (DM.q n ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) hA P𝒪) w₁).base (hsq.isoPullback.hom.base x) ∈
          Set.range (Limits.pullback.snd (DM.q n ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) hA P𝒪) w₁).base := ⟨_, rfl⟩
      rw [Scheme.Pullback.range_snd] at this
      exact this
    · intro hy
      have : y ∈ Set.range (Limits.pullback.snd (DM.q n ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) hA P𝒪) w₁).base := by
        rw [Scheme.Pullback.range_snd]; exact hy
      obtain ⟨z, rfl⟩ := this
      obtain ⟨x, rfl⟩ := (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso hsq.isoPullback)).surjective z
      exact ⟨x, rfl⟩
  refine ⟨by rw [hκ]; infer_instance, ?_⟩
  rw [hκ]
  ext y
  simp only [Set.mem_range, Scheme.Hom.comp_apply, Set.mem_image]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, hrange_j ▸ ⟨x, rfl⟩, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    rw [← hrange_j] at hw
    obtain ⟨x, rfl⟩ := hw
    exact ⟨x, rfl⟩

section Generic
open CategoryTheory.Limits

theorem range_eq_preimage_of_isPullback {P X Y Z : Scheme.{0}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) :
    Set.range fst.base = f.base ⁻¹' Set.range g.base := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨snd.base p, ?_⟩
    have e := congrArg (fun k => k.base p) h.w
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at e
    exact e.symm
  · rintro ⟨y, hy⟩
    obtain ⟨p, hp, -⟩ := Scheme.exists_preimage_of_isPullback h x y hy.symm
    exact ⟨p, hp⟩

theorem twoSheets {B C D P Z W Xn X' : Scheme.{0}}
    {cB : C ⟶ B} {dB : D ⟶ B} {fst : P ⟶ C} {snd : P ⟶ D} (hP : IsPullback fst snd cB dB)
    (sp sm : D ⟶ P) (hsp : sp ≫ snd = 𝟙 D) (hsm : sm ≫ snd = 𝟙 D)
    [IsOpenImmersion sp] [IsOpenImmersion sm]
    (hcov : ∀ p : P, p ∈ Set.range sp.base ∨ p ∈ Set.range sm.base)
    (hdisj : Set.range sp.base ∩ Set.range sm.base = ∅)
    {zB : Z ⟶ B} {w₁ : W ⟶ Z} {w₂ : W ⟶ D} (hW : IsPullback w₁ w₂ zB dB)
    {p₁ : Xn ⟶ Z} {p₂ : Xn ⟶ C} (hXn : IsPullback p₁ p₂ zB cB)
    {xbn : Xn ⟶ B} (hxbn : xbn = p₁ ≫ zB)
    {q : X' ⟶ Xn} {x' : X' ⟶ D} (hX' : IsPullback q x' xbn dB) :
    ∃ ιp ιm : W ⟶ X',
      IsOpenImmersion ιp ∧ IsOpenImmersion ιm ∧
      ιp ≫ q ≫ p₁ = w₁ ∧ ιp ≫ x' = w₂ ∧ ιp ≫ q ≫ p₂ = w₂ ≫ sp ≫ fst ∧
      ιm ≫ q ≫ p₁ = w₁ ∧ ιm ≫ x' = w₂ ∧ ιm ≫ q ≫ p₂ = w₂ ≫ sm ≫ fst ∧
      (∀ x : X', x ∈ Set.range ιp.base ∨ x ∈ Set.range ιm.base) ∧
      Set.range ιp.base ∩ Set.range ιm.base = ∅ ∧
      (∀ (g : X' ⟶ X') (t : C ⟶ C), t ≫ cB = cB → g ≫ x' = x' → g ≫ q ≫ p₂ = q ≫ p₂ ≫ t →
        (sp ≫ fst ≫ t = sp ≫ fst → g.base '' Set.range ιp.base ⊆ Set.range ιp.base) ∧
        (sp ≫ fst ≫ t = sm ≫ fst → g.base '' Set.range ιp.base ⊆ Set.range ιm.base) ∧
        (sm ≫ fst ≫ t = sp ≫ fst → g.base '' Set.range ιm.base ⊆ Set.range ιp.base)) := by
  have hxbn' : xbn = p₂ ≫ cB := hxbn.trans hXn.w

  let u : X' ⟶ P := hP.lift (q ≫ p₂) x' (by rw [Category.assoc, ← hxbn']; exact hX'.w)
  have hu₁ : u ≫ fst = q ≫ p₂ := hP.lift_fst _ _ _
  have hu₂ : u ≫ snd = x' := hP.lift_snd _ _ _
  let ω : X' ⟶ W := hW.lift (q ≫ p₁) x' (by rw [Category.assoc, ← hxbn]; exact hX'.w)
  have hω₁ : ω ≫ w₁ = q ≫ p₁ := hW.lift_fst _ _ _
  have hω₂ : ω ≫ w₂ = x' := hW.lift_snd _ _ _

  have LEFT : IsPullback q u p₂ fst := by
    refine IsPullback.of_bot ?_ hu₁.symm hP
    rw [hu₂, ← hxbn']
    exact hX'

  have BIG : IsPullback (q ≫ p₁) u zB (fst ≫ cB) := LEFT.paste_horiz hXn

  have SQ : IsPullback ω u w₂ snd := by
    refine IsPullback.of_right ?_ (hω₂.trans hu₂.symm) hW
    rw [hω₁, ← hP.w]
    exact BIG

  have key : ∀ (s : D ⟶ P), s ≫ snd = 𝟙 D → IsOpenImmersion s →
      ∃ ι : W ⟶ X', IsOpenImmersion ι ∧ ι ≫ ω = 𝟙 W ∧ ι ≫ u = w₂ ≫ s ∧
        Set.range ι.base = u.base ⁻¹' Set.range s.base := by
    intro s hs hso
    let ι : W ⟶ X' := SQ.lift (𝟙 W) (w₂ ≫ s) (by rw [Category.id_comp, Category.assoc, hs, Category.comp_id])
    have hι₁ : ι ≫ ω = 𝟙 W := SQ.lift_fst _ _ _
    have hι₂ : ι ≫ u = w₂ ≫ s := SQ.lift_snd _ _ _
    have SQs : IsPullback ι w₂ u s := by
      refine IsPullback.of_right ?_ hι₂ SQ
      rw [hι₁, hs]
      exact IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, Category.comp_id]⟩
    exact ⟨ι, MorphismProperty.of_isPullback (P := @IsOpenImmersion) SQs.flip hso, hι₁, hι₂,
      range_eq_preimage_of_isPullback SQs⟩
  obtain ⟨ιp, hιpo, hιp₁, hιp₂, hrp⟩ := key sp hsp inferInstance
  obtain ⟨ιm, hιmo, hιm₁, hιm₂, hrm⟩ := key sm hsm inferInstance
  refine ⟨ιp, ιm, hιpo, hιmo, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hω₁, ← Category.assoc, hιp₁, Category.id_comp]
  · rw [← hω₂, ← Category.assoc, hιp₁, Category.id_comp]
  · rw [← hu₁, ← Category.assoc, hιp₂, Category.assoc]
  · rw [← hω₁, ← Category.assoc, hιm₁, Category.id_comp]
  · rw [← hω₂, ← Category.assoc, hιm₁, Category.id_comp]
  · rw [← hu₁, ← Category.assoc, hιm₂, Category.assoc]
  · intro x
    rcases hcov (u.base x) with h | h
    · left; rw [hrp]; exact h
    · right; rw [hrm]; exact h
  · rw [hrp, hrm, ← Set.preimage_inter, hdisj, Set.preimage_empty]
  · intro g t ht hg₂ hg₁

    let τ : P ⟶ P := hP.lift (fst ≫ t) snd (by rw [Category.assoc, ht]; exact hP.w)
    have hgu : g ≫ u = u ≫ τ := by
      apply hP.hom_ext
      · rw [Category.assoc, hu₁, hg₁, Category.assoc, hP.lift_fst, reassoc_of% hu₁]
      · rw [Category.assoc, hu₂, hg₂, Category.assoc, hP.lift_snd, hu₂]
    have move : ∀ (s s' : D ⟶ P) (ι ι' : W ⟶ X'), s ≫ snd = 𝟙 D → s' ≫ snd = 𝟙 D →
        ι ≫ u = w₂ ≫ s → Set.range ι'.base = u.base ⁻¹' Set.range s'.base →
        s ≫ fst ≫ t = s' ≫ fst → g.base '' Set.range ι.base ⊆ Set.range ι'.base := by
      intro s s' ι ι' hs hs' hιu hr' hst
      have hsτ : s ≫ τ = s' := by
        apply hP.hom_ext
        · rw [Category.assoc, hP.lift_fst, hst]
        · rw [Category.assoc, hP.lift_snd, hs, hs']
      rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
      rw [hr', Set.mem_preimage]
      refine ⟨w₂.base w, ?_⟩
      have e1 : ι ≫ g ≫ u = w₂ ≫ s' := by rw [hgu, ← Category.assoc, hιu, Category.assoc, hsτ]
      have e2 := congrArg (fun k => k.base w) e1
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at e2
      exact e2.symm
    exact ⟨move sp sp ιp ιp hsp hsp hιp₂ hrp, move sp sm ιp ιm hsp hsm hιp₂ hrm, move sm sp ιm ιp hsm hsp hιm₂ hrp⟩

theorem isPullback_comp_mono {C : Type*} [Category C] {P X Y B B' : C} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ B} {g : Y ⟶ B} (h : IsPullback fst snd f g) (m : B ⟶ B') [Mono m] :
    IsPullback fst snd (f ≫ m) (g ≫ m) :=
  IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono f g m h.cone h.isLimit)

theorem spec_fst_snd (R : Type) [CommRing R] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (RingHom.fst R R))) ∧
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (RingHom.snd R R))) ∧
    (∀ p : Spec (CommRingCat.of (R × R)), p ∈ Set.range (Spec.map (CommRingCat.ofHom (RingHom.fst R R))).base ∨
      p ∈ Set.range (Spec.map (CommRingCat.ofHom (RingHom.snd R R))).base) ∧
    Set.range (Spec.map (CommRingCat.ofHom (RingHom.fst R R))).base ∩
      Set.range (Spec.map (CommRingCat.ofHom (RingHom.snd R R))).base = ∅ := by
  have h₁ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (RingHom.fst R R))) := by
    letI := (RingHom.fst R R).toAlgebra
    exact IsOpenImmersion.of_isLocalization (1, 0)
  have h₂ : IsOpenImmersion (Spec.map (CommRingCat.ofHom (RingHom.snd R R))) := by
    letI := (RingHom.snd R R).toAlgebra
    exact IsOpenImmersion.of_isLocalization (0, 1)
  let e := asIso (coprodSpec R R)
  have hc := isCompl_range_inl_inr (Spec (CommRingCat.of R)) (Spec (CommRingCat.of R))
  refine ⟨h₁, h₂, ?_, ?_⟩
  · intro p
    have hp : e.inv.base p ∈ Set.range (coprod.inl : Spec (.of R) ⟶ Spec (.of R) ⨿ Spec (.of R)).base ⊔
        Set.range (coprod.inr : Spec (.of R) ⟶ Spec (.of R) ⨿ Spec (.of R)).base := by
      rw [hc.sup_eq_top]; trivial
    have hback : ∀ y, e.hom.base (e.inv.base y) = y := fun y => by
      rw [← TopCat.comp_app, ← Scheme.Hom.comp_base, e.inv_hom_id]; rfl
    rcases hp with ⟨y, hy⟩ | ⟨y, hy⟩
    · left
      refine ⟨y, ?_⟩
      rw [← coprodSpec_inl, Scheme.Hom.comp_base, TopCat.comp_app, hy]
      exact hback p
    · right
      refine ⟨y, ?_⟩
      rw [← coprodSpec_inr, Scheme.Hom.comp_base, TopCat.comp_app, hy]
      exact hback p
  · rw [← Set.disjoint_iff_inter_eq_empty, Set.disjoint_iff_forall_ne]
    rintro _ ⟨y, rfl⟩ _ ⟨y', rfl⟩ heq
    rw [← coprodSpec_inl, ← coprodSpec_inr, Scheme.Hom.comp_base, Scheme.Hom.comp_base, TopCat.comp_app, TopCat.comp_app] at heq
    have hinj : Function.Injective (coprodSpec R R).base := (Scheme.homeoOfIso e).injective
    exact Set.disjoint_iff_forall_ne.mp hc.disjoint ⟨y, rfl⟩ ⟨y', rfl⟩ (hinj heq)

set_option maxHeartbeats 3200000 in

theorem sheetBase {𝒪 A S : Type} [CommRing 𝒪] [CommRing A] [CommRing S] [Algebra 𝒪 A] [Algebra 𝒪 S]
    (ip im : A →ₐ[𝒪] S)
    (hG3 : Function.Bijective (Algebra.TensorProduct.lift (ip.prod im) ((AlgHom.id 𝒪 S).prod (AlgHom.id 𝒪 S)) (fun _ _ => Commute.all _ _)))
    (c : 𝒪) (I : Ideal A) (J : Ideal S) (hcI : algebraMap 𝒪 A c ∈ I) (hJ : J = Ideal.span {algebraMap 𝒪 S c})
    (fp fm : A →+* S) (hfp : ∀ x, fp x = ip x) (hfm : ∀ x, fm x = im x)
    (hp : I ≤ J.comap fp) (hm : I ≤ J.comap fm) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (RingHom.prod (Ideal.quotientMap J fp hp) (Ideal.quotientMap J fm hm))))
      (Spec.map (CommRingCat.ofHom (algebraMap (S ⧸ J) ((S ⧸ J) × (S ⧸ J)))))
      (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (A ⧸ I))))
      (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (S ⧸ J)))) := by
  have hp' : I ≤ J.comap ip.toRingHom := fun x hx => by
    have := hp hx; rw [Ideal.mem_comap] at this ⊢; rw [hfp] at this; exact this
  have hm' : I ≤ J.comap im.toRingHom := fun x hx => by
    have := hm hx; rw [Ideal.mem_comap] at this ⊢; rw [hfm] at this; exact this
  let ep : (A ⧸ I) →ₐ[𝒪] (S ⧸ J) := Ideal.quotientMapₐ J ip hp'
  let em : (A ⧸ I) →ₐ[𝒪] (S ⧸ J) := Ideal.quotientMapₐ J im hm'
  let ε : (A ⧸ I) →ₐ[𝒪] (S ⧸ J) × (S ⧸ J) := ep.prod em
  let δ : (S ⧸ J) →ₐ[𝒪] (S ⧸ J) × (S ⧸ J) := (AlgHom.id 𝒪 (S ⧸ J)).prod (AlgHom.id 𝒪 (S ⧸ J))
  let Λ : (A ⧸ I) ⊗[𝒪] (S ⧸ J) →ₐ[𝒪] (S ⧸ J) × (S ⧸ J) := Algebra.TensorProduct.lift ε δ (fun _ _ => Commute.all _ _)
  have hΛ : ∀ (x : A ⧸ I) (y : S ⧸ J), Λ (x ⊗ₜ y) = ε x * δ y := fun x y => Algebra.TensorProduct.lift_tmul _ _ _ x y
  have hε : ∀ a : A, ε (Ideal.Quotient.mk I a) = (Ideal.Quotient.mk J (ip a), Ideal.Quotient.mk J (im a)) := fun a => rfl
  have hδ : ∀ y : S ⧸ J, δ y = (y, y) := fun y => rfl

  let ρ : A ⊗[𝒪] S →ₐ[𝒪] (A ⧸ I) ⊗[𝒪] (S ⧸ J) :=
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ 𝒪 I) (Ideal.Quotient.mkₐ 𝒪 J)
  let red : S × S →ₐ[𝒪] (S ⧸ J) × (S ⧸ J) :=
    ((Ideal.Quotient.mkₐ 𝒪 J).comp (AlgHom.fst 𝒪 S S)).prod ((Ideal.Quotient.mkₐ 𝒪 J).comp (AlgHom.snd 𝒪 S S))
  have hred : ∀ p : S × S, red p = (Ideal.Quotient.mk J p.1, Ideal.Quotient.mk J p.2) := fun p => rfl
  have hsq : Λ.comp ρ = red.comp (Algebra.TensorProduct.lift (ip.prod im) ((AlgHom.id 𝒪 S).prod (AlgHom.id 𝒪 S)) (fun _ _ => Commute.all _ _)) := by
    apply Algebra.TensorProduct.ext'
    intro a u
    rw [AlgHom.comp_apply, AlgHom.comp_apply, Algebra.TensorProduct.lift_tmul, hred]
    change Λ (Ideal.Quotient.mk I a ⊗ₜ Ideal.Quotient.mk J u) = _
    rw [hΛ, hε, hδ, Prod.mk_mul_mk, AlgHom.prod_apply, AlgHom.prod_apply, AlgHom.id_apply, Prod.mk_mul_mk, map_mul, map_mul]
  have hρ : Function.Surjective ρ :=
    TensorProduct.map_surjective (Ideal.Quotient.mkₐ_surjective 𝒪 _) (Ideal.Quotient.mkₐ_surjective 𝒪 _)
  have hΛsurj : Function.Surjective Λ := by
    intro z
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective z.1
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective z.2
    obtain ⟨t, ht⟩ := hG3.2 (a, b)
    refine ⟨ρ t, ?_⟩
    rw [← AlgHom.comp_apply, hsq, AlgHom.comp_apply, ht, hred]
    exact Prod.ext ha hb
  have hcAI : algebraMap 𝒪 (A ⧸ I) c = 0 := by
    rw [IsScalarTower.algebraMap_apply 𝒪 A (A ⧸ I), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hcI
  have hΛinj : Function.Injective Λ := by
    rw [injective_iff_map_eq_zero]
    intro s hs
    obtain ⟨t, rfl⟩ := hρ s
    have h1 : red (Algebra.TensorProduct.lift (ip.prod im) ((AlgHom.id 𝒪 S).prod (AlgHom.id 𝒪 S)) (fun _ _ => Commute.all _ _) t) = 0 := by
      rw [← AlgHom.comp_apply, ← hsq, AlgHom.comp_apply]; exact hs
    rw [hred, Prod.ext_iff] at h1
    obtain ⟨h1a, h1b⟩ := h1
    simp only [Prod.fst_zero, Prod.snd_zero, Ideal.Quotient.eq_zero_iff_mem, hJ, Ideal.mem_span_singleton'] at h1a h1b
    obtain ⟨a', ha'⟩ := h1a
    obtain ⟨b', hb'⟩ := h1b
    obtain ⟨t', ht'⟩ := hG3.2 (a', b')
    have htt : t = c • t' := by
      apply hG3.1
      rw [Algebra.smul_def, map_mul, AlgHom.commutes, ht', Prod.algebraMap_apply, Prod.mk_mul_mk,
        mul_comm _ a', mul_comm _ b', ha', hb']
    rw [htt, Algebra.smul_def, map_mul, AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply, hcAI,
      TensorProduct.zero_tmul, zero_mul]
  let eΛ : (A ⧸ I) ⊗[𝒪] (S ⧸ J) ≃+* (S ⧸ J) × (S ⧸ J) := RingEquiv.ofBijective Λ.toRingHom ⟨hΛinj, hΛsurj⟩
  have hPO : IsPushout (CommRingCat.ofHom (algebraMap 𝒪 (A ⧸ I))) (CommRingCat.ofHom (algebraMap 𝒪 (S ⧸ J)))
      (CommRingCat.ofHom ε.toRingHom) (CommRingCat.ofHom (algebraMap (S ⧸ J) ((S ⧸ J) × (S ⧸ J)))) := by
    refine (CommRingCat.isPushout_tensorProduct 𝒪 (A ⧸ I) (S ⧸ J)).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      eΛ.toCommRingCatIso (by simp) (by simp) ?_ ?_
    · ext x
      · change (Λ (Ideal.Quotient.mk I x ⊗ₜ 1)).1 = (ε (Ideal.Quotient.mk I x)).1
        rw [hΛ, map_one, mul_one]
      · change (Λ (Ideal.Quotient.mk I x ⊗ₜ 1)).2 = (ε (Ideal.Quotient.mk I x)).2
        rw [hΛ, map_one, mul_one]
    · ext y
      · change (Λ (1 ⊗ₜ Ideal.Quotient.mk J y)).1 = ((Ideal.Quotient.mk J y, Ideal.Quotient.mk J y) : (S ⧸ J) × (S ⧸ J)).1
        rw [hΛ, map_one, one_mul, hδ]
      · change (Λ (1 ⊗ₜ Ideal.Quotient.mk J y)).2 = ((Ideal.Quotient.mk J y, Ideal.Quotient.mk J y) : (S ⧸ J) × (S ⧸ J)).2
        rw [hΛ, map_one, one_mul, hδ]
  have hεeq : ε.toRingHom = RingHom.prod (Ideal.quotientMap J fp hp) (Ideal.quotientMap J fm hm) := by
    apply Ideal.Quotient.ringHom_ext
    ext a
    · change (ε (Ideal.Quotient.mk I a)).1 = Ideal.Quotient.mk J (fp a)
      rw [hε, hfp]
    · change (ε (Ideal.Quotient.mk I a)).2 = Ideal.Quotient.mk J (fm a)
      rw [hε, hfm]
  rw [hεeq] at hPO
  exact isPullback_SpecMap_of_isPushout _ _ _ _ hPO

end Generic

theorem frobParity (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr) (n : ℕ)
    (Fr₂n : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) ≃ₐ[𝒪] (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}))
    (hFr₂n : ∀ (y y' : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))), (y' : Onr) = Fr (y : Onr) → Fr₂n (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ y')
    (v : ℤ) :
    (((Fr₂n ^ (- v)).toRingEquiv.toRingHom).comp (algebraMap 𝒪 (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})) = algebraMap 𝒪 (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})) ∧
    (Even v → RingHom.comp (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) ((AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val.toRingHom) (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)) ((Fr₂n ^ (- v)).toRingEquiv.toRingHom) = (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) ((AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val.toRingHom) (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))) ∧
    (¬ Even v → RingHom.comp (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) ((AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val.toRingHom) (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)) ((Fr₂n ^ (- v)).toRingEquiv.toRingHom) = (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) ((Fr : Onr →ₐ[𝒪] Onr).toRingHom.comp (AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val.toRingHom) (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span (by simp)))) ∧
    (¬ Even v → RingHom.comp (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) ((Fr : Onr →ₐ[𝒪] Onr).toRingHom.comp (AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val.toRingHom) (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span (by simp))) ((Fr₂n ^ (- v)).toRingEquiv.toRingHom) = (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) ((AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val.toRingHom) (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))) := by
  classical

  have hmem : ∀ y : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)), Fr (y : Onr) ∈ (AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) := by
    intro y
    have hy := (AlgHom.mem_equalizer _ _ _).mp y.2
    rw [AlgHom.mem_equalizer]
    simp only [AlgEquiv.coe_algHom, AlgEquiv.trans_apply, AlgHom.id_apply] at hy ⊢
    rw [hy]
  have hsq : ∀ y : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)), Fr (Fr (y : Onr)) = (y : Onr) := by
    intro y
    have hy := (AlgHom.mem_equalizer _ _ _).mp y.2
    simpa only [AlgEquiv.coe_algHom, AlgEquiv.trans_apply, AlgHom.id_apply] using hy
  have hF1 : ∀ y : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)), Fr₂n (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ (⟨Fr (y : Onr), hmem y⟩ : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) :=
    fun y => hFr₂n y ⟨Fr (y : Onr), hmem y⟩ rfl
  have hFF : Fr₂n * Fr₂n = 1 := by
    apply AlgEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [AlgEquiv.mul_apply, hF1, hF1, AlgEquiv.one_apply]
    congr 1
    exact Subtype.ext (hsq y)

  have hpow : Fr₂n ^ (-v) = if Even v then 1 else Fr₂n := by
    have h2 : Fr₂n ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hFF
    split_ifs with hv
    · obtain ⟨k, rfl⟩ := hv
      rw [← two_mul, neg_mul_eq_mul_neg, zpow_mul, h2, one_zpow]
    · obtain ⟨k, rfl⟩ := Int.not_even_iff_odd.mp hv
      rw [neg_add, zpow_add, ← mul_neg, zpow_mul, h2, one_zpow, one_mul, zpow_neg, zpow_one]
      exact inv_eq_of_mul_eq_one_right hFF
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext a
    exact (Fr₂n ^ (-v)).commutes a
  · intro hv
    rw [hpow, if_pos hv]
    apply Ideal.Quotient.ringHom_ext
    ext y
    rfl
  · intro hv
    rw [hpow, if_neg hv]
    apply Ideal.Quotient.ringHom_ext
    ext y
    have e1 : Fr₂n.toRingEquiv.toRingHom (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) y) =
        Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) (⟨Fr (y : Onr), hmem y⟩ : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) := hF1 y
    simp only [RingHom.comp_apply, e1, Ideal.quotientMap_mk]
    rfl
  · intro hv
    rw [hpow, if_neg hv]
    apply Ideal.Quotient.ringHom_ext
    ext y
    have e1 : Fr₂n.toRingEquiv.toRingHom (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) y) =
        Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) (⟨Fr (y : Onr), hmem y⟩ : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) := hF1 y
    simp only [RingHom.comp_apply, e1, Ideal.quotientMap_mk]
    show Ideal.Quotient.mk _ (Fr (Fr (y : Onr))) = Ideal.Quotient.mk _ (y : Onr)
    rw [hsq]

set_option maxHeartbeats 6400000 in

theorem sheets

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
    (n : ℕ) (X'n : Scheme.{0}) (xb'n : X'n ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}))) (qXn : X'n ⟶ X n)
    (hqn : IsPullback qXn xb'n (xb n) (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) (algebraMap 𝒪 Onr)
        (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))))
    (a'n : G₂ →* Aut (X'n)) (hq_a : ∀ g : G₂, (a'n g).hom ≫ qXn = qXn ≫ (a n g).hom)
    (ha'_over : ∀ g : G₂, (a'n g).hom ≫ xb'n = xb'n)
    (W : Scheme.{0}) (w₁ : W ⟶ DM.Z n) (w₂ : W ⟶ Spec (CommRingCat.of (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)})))
    (hW : IsPullback w₁ w₂ (DM.zb n) (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) (algebraMap 𝒪 Onr)
        (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))))) :
    ∃ ιp ιm : W ⟶ X'n,
      IsOpenImmersion ιp ∧ IsOpenImmersion ιm ∧
      ιp ≫ qXn ≫ pr₁ n = w₁ ∧ ιp ≫ xb'n = w₂ ∧
      ιp ≫ qXn ≫ pr₂ n = w₂ ≫ Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) ((AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val.toRingHom)
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))) ∧
      ιm ≫ qXn ≫ pr₁ n = w₁ ∧ ιm ≫ xb'n = w₂ ∧
      ιm ≫ qXn ≫ pr₂ n = w₂ ≫ Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) ((Fr : Onr →ₐ[𝒪] Onr).toRingHom.comp (AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val.toRingHom)
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span (by simp)))) ∧
      (∀ x : X'n, x ∈ Set.range ιp.base ∨ x ∈ Set.range ιm.base) ∧
      Set.range ιp.base ∩ Set.range ιm.base = ∅ ∧
      (∀ γ : ↥Γ, Even (Multiplicative.toAdd (vdet (σ (γ : G)))) →
          (a'n (θ γ)).hom.base '' Set.range ιp.base ⊆ Set.range ιp.base) ∧
      (∀ γ : ↥Γ, ¬ Even (Multiplicative.toAdd (vdet (σ (γ : G)))) →
          (a'n (θ γ)).hom.base '' Set.range ιp.base ⊆ Set.range ιm.base) ∧
      (∀ γ : ↥Γ, ¬ Even (Multiplicative.toAdd (vdet (σ (γ : G)))) →
          (a'n (θ γ)).hom.base '' Set.range ιm.base ⊆ Set.range ιp.base) := by

  have hG3 := CerednikDrinfeld.UnramQuad.bijective_lift_prod_equalizer_frobenius_sq_tensor 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr
    hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr

  have hP := sheetBase ((AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val) ((Fr : Onr →ₐ[𝒪] Onr).comp (AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val) hG3 (π ^ (n + 1))
    (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) (by rw [map_pow]; exact Ideal.mem_span_singleton_self _) (by rw [map_pow])
    ((AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val.toRingHom) ((Fr : Onr →ₐ[𝒪] Onr).toRingHom.comp (AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val.toRingHom) (fun _ => rfl) (fun _ => rfl)
    (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)
    (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span (by simp))
  obtain ⟨hos₁, hos₂, hcovP, hdisjP⟩ := spec_fst_snd (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)})
  have hsp : (Spec.map (CommRingCat.ofHom (RingHom.fst (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)})))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) ((Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) × (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}))))) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id, ← CommRingCat.ofHom_id]; rfl
  have hsm : (Spec.map (CommRingCat.ofHom (RingHom.snd (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)})))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) ((Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) × (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}))))) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id, ← CommRingCat.ofHom_id]; rfl
  have hspf : (Spec.map (CommRingCat.ofHom (RingHom.fst (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)})))) ≫ (Spec.map (CommRingCat.ofHom (RingHom.prod (Ideal.quotientMap (I := Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) ((AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val.toRingHom) (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)) (Ideal.quotientMap (I := Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) ((Fr : Onr →ₐ[𝒪] Onr).toRingHom.comp (AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val.toRingHom) (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span (by simp)))))) = Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I := Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) ((AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val.toRingHom) (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl
  have hsmf : (Spec.map (CommRingCat.ofHom (RingHom.snd (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)})))) ≫ (Spec.map (CommRingCat.ofHom (RingHom.prod (Ideal.quotientMap (I := Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) ((AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val.toRingHom) (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)) (Ideal.quotientMap (I := Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) ((Fr : Onr →ₐ[𝒪] Onr).toRingHom.comp (AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val.toRingHom) (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span (by simp)))))) = Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I := Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) ((Fr : Onr →ₐ[𝒪] Onr).toRingHom.comp (AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)).val.toRingHom) (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span (by simp)))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have eC : Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))) (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))) = (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl
  have eD : Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) (algebraMap 𝒪 Onr) (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))) = (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)})))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl
  have hX𝒪 : IsPullback (pr₁ n) (pr₂ n) (DM.zb n ≫ (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))))) (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})))) := by
    rw [← eC]; exact isPullback_comp_mono (hX n) _
  have hW𝒪 : IsPullback w₁ w₂ (DM.zb n ≫ (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))))) (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)})))) := by
    rw [← eD]; exact isPullback_comp_mono hW _
  have hq𝒪 : IsPullback qXn xb'n (xb n ≫ (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))))) (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)})))) := by
    rw [← eD]; exact isPullback_comp_mono hqn _
  have hxbn : xb n ≫ (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))) = pr₁ n ≫ DM.zb n ≫ (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)})))) := by rw [hxb n, Category.assoc]

  obtain ⟨ιp, ιm, hιpo, hιmo, c1, c2, c3, c4, c5, c6, hcov, hdisj, hpar⟩ :=
    twoSheets hP (Spec.map (CommRingCat.ofHom (RingHom.fst (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)})))) (Spec.map (CommRingCat.ofHom (RingHom.snd (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) (Onr ⧸ Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)})))) hsp hsm hcovP hdisjP hW𝒪 hX𝒪 hxbn hq𝒪
  refine ⟨ιp, ιm, hιpo, hιmo, c1, c2, ?_, c4, c5, ?_, hcov, hdisj, ?_, ?_, ?_⟩
  · rw [c3, hspf]
  · rw [c6, hsmf]
  · intro γ hev
    obtain ⟨hFa, hFe, -, -⟩ := frobParity 𝒪 π Onr Fr n (Fr₂ n) (hFr₂ n) (Multiplicative.toAdd (vdet (σ (γ : G))))
    obtain ⟨P1, -, -⟩ := hpar (a'n (θ γ)).hom (Spec.map (CommRingCat.ofHom (((Fr₂ n) ^ (- Multiplicative.toAdd (vdet (σ (γ : G))))).toRingEquiv.toRingHom)))
      (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hFa]) (ha'_over (θ γ))
      (by rw [← Category.assoc, hq_a, Category.assoc, ha_pr₂])
    exact P1 (by rw [← Category.assoc, hspf, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hFe hev])
  · intro γ hodd'
    obtain ⟨hFa, -, hFo, -⟩ := frobParity 𝒪 π Onr Fr n (Fr₂ n) (hFr₂ n) (Multiplicative.toAdd (vdet (σ (γ : G))))
    obtain ⟨-, P2, -⟩ := hpar (a'n (θ γ)).hom (Spec.map (CommRingCat.ofHom (((Fr₂ n) ^ (- Multiplicative.toAdd (vdet (σ (γ : G))))).toRingEquiv.toRingHom)))
      (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hFa]) (ha'_over (θ γ))
      (by rw [← Category.assoc, hq_a, Category.assoc, ha_pr₂])
    exact P2 (by rw [← Category.assoc, hspf, hsmf, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hFo hodd'])
  · intro γ hodd'
    obtain ⟨hFa, -, -, hFo⟩ := frobParity 𝒪 π Onr Fr n (Fr₂ n) (hFr₂ n) (Multiplicative.toAdd (vdet (σ (γ : G))))
    obtain ⟨-, -, P3⟩ := hpar (a'n (θ γ)).hom (Spec.map (CommRingCat.ofHom (((Fr₂ n) ^ (- Multiplicative.toAdd (vdet (σ (γ : G))))).toRingEquiv.toRingHom)))
      (by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hFa]) (ha'_over (θ γ))
      (by rw [← Category.assoc, hq_a, Category.assoc, ha_pr₂])
    exact P3 (by rw [← Category.assoc, hsmf, hspf, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hFo hodd'])

theorem aut_hom_inv_base {Y : Scheme.{0}} {G : Type} [Group G] (a : G →* Aut Y) (g : G) (x : Y) :
    (a g⁻¹).hom.base ((a g).hom.base x) = x := by
  rw [← Scheme.Hom.comp_apply, ← Iso.trans_hom, ← CategoryTheory.Aut.Aut_mul_def, ← map_mul, inv_mul_cancel, map_one]
  rfl

end D1Body

set_option maxHeartbeats 12800000 in
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
    :
    Nonempty (MumfordTower.NrPresentation 𝒪 π K₀ g₁ N DM Onr Fr X xb xt G₂ a pr₁ pr₂ ((Γ'.subgroupOf Γ).map θ)) := by
  classical
  haveI := hdvr
  have hG1 := AlgebraicGeometry.exists_tower_baseChange_of_isPullback 𝒪 π X xb xt hcart G₂ a ha_over ha_xt Onr
  obtain ⟨X', xb', xt', a', qX, hq, hcart', hq_xt, hq_a, ha'_over, ha'_xt⟩ := hG1
  have key := fun (n : ℕ) (h : Matrix.GeneralLinearGroup (Fin 2) K₀) =>
    D1Body.chartData 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet G σ Γ hcent hodd Γ' hΓ' ρ hρ hdisc hcocpt g₁ hg₁ N hNle hNnorm hNidx DM X xb xt G₂ a pr₁ pr₂ θ Fr₂ hcart hproper hflat haff ha_over ha_xt hX hxb hxt₁ hxt₂ hθsurj hθker hFr₂ ha_pr₂ ha_pr₁ n (X' n) (xb' n) (qX n) (hq n) h
  choose κ' hκ₁ hκ₂ hκ₃ using key
  have keyS := fun (n : ℕ) =>
    D1Body.sheets 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet G σ Γ hcent hodd Γ' hΓ' ρ hρ hdisc hcocpt g₁ hg₁ N hNle hNnorm hNidx DM X xb xt G₂ a pr₁ pr₂ θ Fr₂ hcart hproper hflat haff ha_over ha_xt hX hxb hxt₁ hxt₂ hθsurj hθker hFr₂ ha_pr₂ ha_pr₁ n (X' n) (xb' n) (qX n) (hq n) (a' n) (hq_a n) (ha'_over n)
      (Limits.pullback (DM.zb n) (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) (algebraMap 𝒪 Onr)
        (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))))
      (Limits.pullback.fst _ _) (Limits.pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  choose ιp ιm hS using keyS

  have hA : ∀ n : ℕ, (algebraMap 𝒪 ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) π) ^ (n + 1) = 0 := fun n =>
    (map_pow (Ideal.Quotient.mk (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) _ (n + 1)).symm.trans
      (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _))
  have keyD := fun (n : ℕ) (h : Matrix.GeneralLinearGroup (Fin 2) K₀) =>
    CerednikDrinfeld.FormalOmega.exists_deligneDatum_line_eq_inEdgeChart_of_isNilpotent
      (K := K₀) π hπ r hres g₁ hg₁ ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) ⟨n + 1, hA n⟩ (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))
  choose d𝒪 hd𝒪 using keyD

  have hOI : ∀ (n : ℕ) (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (d P : DeligneDatum (K := K₀) π ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})),
      (d.line (stdFullLattice K₀) =
            Submodule.span ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) {((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
          d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
            (Submodule.span ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) {(1 : ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
              (actBaseChange ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) g₁ (stdFullLattice K₀)).toLinearMap ∧
          d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
      DeligneDatum.IsPullback (K := K₀) (π := π) ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) h⁻¹ d P →
      IsOpenImmersion (κ' n h) ∧ Set.range (κ' n h).base =
        (ιp n).base '' ((Limits.pullback.fst (DM.zb n) (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) (algebraMap 𝒪 Onr)
        (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))))).base ⁻¹'
          Set.range (DM.q n ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) (hA n) P).base) := by
    intro n h d P hd hP
    obtain ⟨hOIp, -, h3, h4, h5, -⟩ := hS n
    haveI := hOIp
    exact D1Body.chart_openImmersion_range 𝒪 hdvr π hπ hcomplete hres hunr K₀ Onr Fr hOnr_complete hOnr_max hOnr_alg hOnr_closed hFr vdet hvdet G σ Γ hcent hodd Γ' hΓ' ρ hρ hdisc hcocpt g₁ hg₁ N hNle hNnorm hNidx DM X xb xt G₂ a pr₁ pr₂ θ Fr₂ hcart hproper hflat haff ha_over ha_xt hX hxb hxt₁ hxt₂ hθsurj hθker hFr₂ ha_pr₂ ha_pr₁ n (X' n) (xb' n) (qX n) (hq n)
      _ _ _ (IsPullback.of_hasPullback _ _) (ιp n) h3 h4 h5
      h (κ' n h) (hκ₁ n h) (hκ₂ n h) (hκ₃ n h) (hA n) d P hd hP

  have hcovp : ∀ (n : ℕ) (y : X' n), y ∈ Set.range (ιp n).base →
      ∃ (h : Matrix.GeneralLinearGroup (Fin 2) K₀) (pt : Spec (CommRingCat.of ((chartERing Onr (algebraMap 𝒪 Onr π) r) ⧸ Ideal.span {(algebraMap Onr (chartERing Onr (algebraMap 𝒪 Onr π) r) (algebraMap 𝒪 Onr π)) ^ (n + 1)}))), (κ' n h).base pt = y := by
    intro n y hy
    obtain ⟨w, rfl⟩ := hy
    obtain ⟨h, d, P, hdP, hPB, hz⟩ := DM.cover n (hA n)
      ((Limits.pullback.fst (DM.zb n) (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 Onr π) ^ (n + 1)}) (algebraMap 𝒪 Onr)
        (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl))))).base w)
    have hr := (hOI n h d P hdP hPB).2
    have : (ιp n).base w ∈ Set.range (κ' n h).base := by
      rw [hr]; exact ⟨w, hz, rfl⟩
    obtain ⟨pt, hpt⟩ := this
    exact ⟨h, pt, hpt⟩
  refine ⟨{
    X' := X'
    xb' := xb'
    xt' := xt'
    a' := a'
    qX := qX
    hq := hq
    hcart' := hcart'
    hq_xt := hq_xt
    hq_a := hq_a
    ha'_over := ha'_over
    κ' := fun h n => κ' n h
    κ'_pr₁ := fun h n => hκ₁ n h
    κ'_pr₂ := fun h n => hκ₂ n h
    κ'_xb' := fun h n => hκ₃ n h
    κ'_isOpenImmersion := fun h n =>
      (hOI n h (d𝒪 n h) (DeligneDatum.pullback π ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) h⁻¹ (d𝒪 n h)) (hd𝒪 n h)
        (DeligneDatum.isPullback_pullback π ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) h⁻¹ (d𝒪 n h))).1
    cover := ?_
    parity := ?_ }⟩
  ·
    intro n x
    obtain ⟨-, -, -, -, -, -, -, -, hcov, -, -, -, hodd2⟩ := hS n
    rcases hcov x with hx | hx
    · obtain ⟨h, pt, hpt⟩ := hcovp n x hx
      refine ⟨1, h, pt, ?_⟩
      rw [map_one, Scheme.Hom.comp_apply, hpt]
      rfl
    · obtain ⟨γ₀, hγ₀Γ, hγ₀v⟩ := hodd
      have hoddγ : ¬ Even (Multiplicative.toAdd (vdet (σ ((⟨γ₀, hγ₀Γ⟩ : ↥Γ) : G)))) := by
        rw [show ((⟨γ₀, hγ₀Γ⟩ : ↥Γ) : G) = γ₀ from rfl, hγ₀v]
        decide
      have hy : (a' n (θ ⟨γ₀, hγ₀Γ⟩)).hom.base x ∈ Set.range (ιp n).base := hodd2 ⟨γ₀, hγ₀Γ⟩ hoddγ ⟨x, hx, rfl⟩
      obtain ⟨h, pt, hpt⟩ := hcovp n _ hy
      refine ⟨(θ ⟨γ₀, hγ₀Γ⟩)⁻¹, h, pt, ?_⟩
      rw [Scheme.Hom.comp_apply, hpt, D1Body.aut_hom_inv_base]
  ·
    intro n g h h' hne
    obtain ⟨y, ⟨p1, hp1⟩, ⟨p2, hp2⟩⟩ := hne
    obtain ⟨γ, rfl⟩ := hθsurj g
    obtain ⟨-, -, -, -, -, -, -, -, -, hdisj, -, hodd1, -⟩ := hS n
    by_cases he : Even (Multiplicative.toAdd (vdet (σ (γ : G))))
    · exact Subgroup.mem_map.mpr ⟨γ, Subgroup.mem_subgroupOf.mpr ((hΓ' γ).mpr ⟨γ.2, he⟩), rfl⟩
    · exfalso
      have hsub : ∀ h₀ : Matrix.GeneralLinearGroup (Fin 2) K₀, Set.range (κ' n h₀).base ⊆ Set.range (ιp n).base := by
        intro h₀
        rw [(hOI n h₀ (d𝒪 n h₀) (DeligneDatum.pullback π ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) h₀⁻¹ (d𝒪 n h₀)) (hd𝒪 n h₀)
          (DeligneDatum.isPullback_pullback π ((chartERing 𝒪 π r) ⧸ Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}) h₀⁻¹ (d𝒪 n h₀))).2]
        exact Set.image_subset_range _ _
      have hy1 : y ∈ Set.range (ιp n).base := hsub h ⟨p1, hp1⟩
      have hy2 : y ∈ Set.range (ιm n).base := by
        refine hodd1 γ he ⟨(κ' n h').base p2, hsub h' ⟨p2, rfl⟩, ?_⟩
        rw [← hp2, Scheme.Hom.comp_apply]
      have : y ∈ Set.range (ιp n).base ∩ Set.range (ιm n).base := ⟨hy1, hy2⟩
      rw [hdisj] at this
      exact this

end S_CerednikDrinfeld_FormalOmega_MumfordTower_nonempty_nrPresentation
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_MumfordTower_nonempty_nrPresentation (solution)
