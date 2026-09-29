-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.MumfordGlueCore.zeta_comp_eq_of_exists_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/a6cd0e72-d76f-58a7-96c7-a083c90348ed

import Definitions.Def_CerednikDrinfeld_MumfordGlueCore
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordVertexType

import Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlueCore_zeta_comp_eq_iff_exists_isPullback_of_isLocalRing
import Theorems.Thm_AlgebraicGeometry_Spec_hom_ext_of_forall_localization_atPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlueCore_zeta_comp_eq_of_exists_isPullback
p2m_attr_erase "instance" "CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.invertible₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₀ CerednikDrinfeld.FormalOmega.DrinfeldDatum.module₁ CerednikDrinfeld.FormalOmega.DrinfeldDatum.addCommGroup₀"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open CategoryTheory AlgebraicGeometry LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Mumford

namespace ZetaRel29

variable {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] (π : 𝒪)

theorem span_image_rTensor_span_singleton {B B' : Type} [CommRing B] [Algebra 𝒪 B] [CommRing B'] [Algebra 𝒪 B']
    (f : B →ₐ[𝒪] B') (M : FullLattice 𝒪 K₀) (v : latticeBaseChange 𝒪 K₀ B M) :
    Submodule.span B' ((LinearMap.rTensor (↥M.1) f.toLinearMap) '' (Submodule.span B {v} : Set (latticeBaseChange 𝒪 K₀ B M))) =
      Submodule.span B' {LinearMap.rTensor (↥M.1) f.toLinearMap v} := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [rTensor_smul_left]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨v, Submodule.subset_span rfl, rfl⟩

theorem isPullback_map {B B' : Type} [CommRing B] [Algebra 𝒪 B] [CommRing B'] [Algebra 𝒪 B']
    (f : B →ₐ[𝒪] B') (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (d d' : DeligneDatum (K := K₀) π B)
    (h : DeligneDatum.IsPullback (K := K₀) (π := π) B g d d') :
    DeligneDatum.IsPullback (K := K₀) (π := π) B' g ((Omega K₀ π).map f d) ((Omega K₀ π).map f d') := by
  have hd' : d' = DeligneDatum.pullback π B g d := DeligneDatum.ext' (funext fun M => h M)
  subst hd'
  show DeligneDatum.IsPullback (K := K₀) (π := π) B' g ((d.map π f)) ((DeligneDatum.pullback π B g d).map π f)
  rw [DeligneDatum.map_pullback]
  exact DeligneDatum.isPullback_pullback π B' g (d.map π f)

theorem inEdgeChart_map {B B' : Type} [CommRing B] [Algebra 𝒪 B] [CommRing B'] [Algebra 𝒪 B']
    (f : B →ₐ[𝒪] B') (d : DeligneDatum (K := K₀) π B) (M' M : FullLattice 𝒪 K₀)
    (h : d.InEdgeChart π M' M) : ((Omega K₀ π).map f d).InEdgeChart π M' M := by
  intro 𝔮 h𝔮
  haveI := h𝔮
  obtain ⟨hle, hπ, h1, h2⟩ := h (Ideal.comap f 𝔮) (Ideal.IsPrime.comap f)
  refine ⟨hle, hπ, fun v hv => ?_, fun v' hv' => ?_⟩
  · rw [← rTensor_one_tmul f M v]
    exact rTensor_not_mem_lineBaseChange_sup f M (d.line M) (d.invertible M) 𝔮 _ (h1 v hv)
  · rw [← rTensor_one_tmul f M' v']
    exact rTensor_not_mem_lineBaseChange_sup f M' (d.line M') (d.invertible M') 𝔮 _ (h2 v' hv')

end ZetaRel29

open ZetaRel29 in

theorem ZetaRel29.ch_map
    {r : ℕ} (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℕ)
    {B C : Type} [CommRing B] [Algebra 𝒪 B] [CommRing C] [Algebra 𝒪 C] (f : B →ₐ[𝒪] C)
    (xq : ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) →ₐ[𝒪] B) (d : DeligneDatum (K := K₀) π B)
    (hd : (d.line (stdFullLattice K₀) =
          Submodule.span B {((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀))) :
    (((Omega K₀ π).map f d).line (stdFullLattice K₀) =
          Submodule.span C {(((f.comp xq).comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : C) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        ((Omega K₀ π).map f d).line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span C {(1 : C) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (((f.comp xq).comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange C g₁ (stdFullLattice K₀)).toLinearMap ∧
        ((Omega K₀ π).map f d).InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) := by
  obtain ⟨h0, h1, h2⟩ := hd
  refine ⟨?_, ?_, inEdgeChart_map π f d _ _ h2⟩
  · show lineBaseChange f _ (d.line _) = _
    rw [h0, lineBaseChange, span_image_rTensor_span_singleton, map_add, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
      AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, map_one]
    rfl
  · show lineBaseChange f _ (d.line _) = _
    rw [h1, lineBaseChange, Submodule.map_span, Set.image_singleton, span_image_rTensor_span_singleton,
      Submodule.map_span, Set.image_singleton, LinearEquiv.coe_coe, LinearEquiv.coe_coe, rTensor_actBaseChange, map_add, LinearMap.rTensor_tmul,
      LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, map_one]
    rfl

theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (g₁ : Matrix.GeneralLinearGroup (Fin 2) K₀) (hg₁ : (g₁ : Matrix (Fin 2) (Fin 2) K₀) = Matrix.diagonal ![algebraMap 𝒪 K₀ π, 1])
    (N : Subgroup (PGL(2, K₀)))
    (hN : IsSchottky (↥N) (BruhatTits.tree 𝒪 K₀))
    (hNtype : N ≤ typePreserving (PGL(2, K₀)) (BruhatTits.tree 𝒪 K₀) (LT.LatticeTree.stdVertex 𝒪 K₀))
    (M : MumfordGlueCore 𝒪 π K₀ r g₁ N) :
    ∀ (n : ℕ) (B : Type) [CommRing B] [Algebra 𝒪 B]
    (h h' : Matrix.GeneralLinearGroup (Fin 2) K₀) (xq xq' : ((chartERing 𝒪 π r) ⧸ (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)})) →ₐ[𝒪] B) (d d' P P' : DeligneDatum (K := K₀) π B),
    (d.line (stdFullLattice K₀) =
          Submodule.span B {((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
    (d'.line (stdFullLattice K₀) =
          Submodule.span B {((xq'.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.ξ 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + (1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 1} ∧
        d'.line (FullLattice.act g₁ (stdFullLattice K₀)) =
          (Submodule.span B {(1 : B) ⊗ₜ[𝒪] stdBasisVec K₀ 0 + ((xq'.comp (Ideal.Quotient.mkₐ 𝒪 (Ideal.span {(algebraMap 𝒪 (chartERing 𝒪 π r) π) ^ (n + 1)}))) (chartERing.η 𝒪 π r)) ⊗ₜ[𝒪] stdBasisVec K₀ 1}).map
            (actBaseChange B g₁ (stdFullLattice K₀)).toLinearMap ∧
        d'.InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀)) →
    DeligneDatum.IsPullback (K := K₀) (π := π) B h⁻¹ d P → DeligneDatum.IsPullback (K := K₀) (π := π) B h'⁻¹ d' P' →
    (∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧ DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P') →
    Spec.map (CommRingCat.ofHom xq.toRingHom) ≫ M.ζ h n = Spec.map (CommRingCat.ofHom xq'.toRingHom) ≫ M.ζ h' n := by
  intro n B _ _ h h' xq xq' d d' P P' hd hd' hP hP' hN
  apply AlgebraicGeometry.Spec_hom_ext_of_forall_localization_atPrime
  intro p
  obtain ⟨g, hg, hgP⟩ := hN
  let φ : B →ₐ[𝒪] Localization.AtPrime p.asIdeal := IsScalarTower.toAlgHom 𝒪 B (Localization.AtPrime p.asIdeal)
  have key := (CerednikDrinfeld.FormalOmega.MumfordGlueCore.zeta_comp_eq_iff_exists_isPullback_of_isLocalRing
    𝒪 hdvr π hπ hres K₀ g₁ hg₁ N hN hNtype M n (Localization.AtPrime p.asIdeal) h h' (φ.comp xq) (φ.comp xq')
    ((Omega K₀ π).map φ d) ((Omega K₀ π).map φ d') ((Omega K₀ π).map φ P) ((Omega K₀ π).map φ P')
    (ZetaRel29.ch_map 𝒪 π K₀ g₁ n φ xq d hd) (ZetaRel29.ch_map 𝒪 π K₀ g₁ n φ xq' d' hd')
    (ZetaRel29.isPullback_map π φ _ _ _ hP) (ZetaRel29.isPullback_map π φ _ _ _ hP')).mpr
    ⟨g, hg, ZetaRel29.isPullback_map π φ _ _ _ hgP⟩
  have e1 : Spec.map (CommRingCat.ofHom (φ.comp xq).toRingHom) =
      Spec.map (CommRingCat.ofHom (algebraMap B (Localization.AtPrime p.asIdeal))) ≫ Spec.map (CommRingCat.ofHom xq.toRingHom) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl
  have e2 : Spec.map (CommRingCat.ofHom (φ.comp xq').toRingHom) =
      Spec.map (CommRingCat.ofHom (algebraMap B (Localization.AtPrime p.asIdeal))) ≫ Spec.map (CommRingCat.ofHom xq'.toRingHom) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl
  rw [e1, e2, Category.assoc, Category.assoc] at key
  exact key

end S_CerednikDrinfeld_FormalOmega_MumfordGlueCore_zeta_comp_eq_of_exists_isPullback
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlueCore_zeta_comp_eq_of_exists_isPullback (solution)
