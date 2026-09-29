-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.MumfordGlueCore.exists_finite_cover_isPullback_of_zeta_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/2cd26e08-8b28-5871-9e47-25e3ba858fc5

import Definitions.Def_CerednikDrinfeld_MumfordGlueCore
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordVertexType

import Theorems.Thm_CerednikDrinfeld_FormalOmega_MumfordGlueCore_zeta_comp_eq_iff_exists_isPullback_of_isLocalRing
import Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_not_mem_forall_lineBaseChange_eq_of_lineBaseChange_localization_eq
import Theorems.Thm_Ideal_exists_finite_span_range_eq_top_of_forall_isPrime_exists_not_mem
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_inEdgeChart_of_line_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlueCore_exists_finite_cover_isPullback_of_zeta_comp_eq
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

namespace OverlapZar29

variable {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] (π : 𝒪)

noncomputable abbrev tr {B : Type} [CommRing B] [Algebra 𝒪 B] (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (d : DeligneDatum (K := K₀) π B) :
    DeligneDatum (K := K₀) π B :=
  (Omega.action K₀ π).act B g d

theorem tr_one {B : Type} [CommRing B] [Algebra 𝒪 B] (d : DeligneDatum (K := K₀) π B) : tr π 1 d = d :=
  (Omega.action K₀ π).act_one B d

theorem tr_mul {B : Type} [CommRing B] [Algebra 𝒪 B] (g h : Matrix.GeneralLinearGroup (Fin 2) K₀) (d : DeligneDatum (K := K₀) π B) :
    tr π (g * h) d = tr π g (tr π h d) := (Omega.action K₀ π).act_mul B g h d

theorem map_tr {B C : Type} [CommRing B] [Algebra 𝒪 B] [CommRing C] [Algebra 𝒪 C] (f : B →ₐ[𝒪] C)
    (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (d : DeligneDatum (K := K₀) π B) :
    (Omega K₀ π).map f (tr π g d) = tr π g ((Omega K₀ π).map f d) :=
  (Omega.action K₀ π).act_map f g d

theorem isPullback_inv_iff {B : Type} [CommRing B] [Algebra 𝒪 B] (g : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (d d' : DeligneDatum (K := K₀) π B) :
    DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ d d' ↔ d' = tr π g d := by
  constructor
  · intro h
    apply DeligneDatum.ext'
    funext M
    exact h M
  · rintro rfl
    exact DeligneDatum.isPullback_pullback π B g⁻¹ d

theorem isPullback_tr_iff {B C : Type} [CommRing B] [Algebra 𝒪 B] [CommRing C] [Algebra 𝒪 C] (f : B →ₐ[𝒪] C)
    (g h h' : Matrix.GeneralLinearGroup (Fin 2) K₀) (d d' : DeligneDatum (K := K₀) π B) :
    DeligneDatum.IsPullback (K := K₀) (π := π) C g⁻¹ ((Omega K₀ π).map f (tr π h d)) ((Omega K₀ π).map f (tr π h' d')) ↔
      (Omega K₀ π).map f d' = tr π (h'⁻¹ * (g * h)) ((Omega K₀ π).map f d) := by
  rw [isPullback_inv_iff, map_tr, map_tr]
  constructor
  · intro e
    rw [tr_mul, tr_mul, ← e, ← tr_mul, inv_mul_cancel, tr_one]
  · intro e
    rw [e, ← tr_mul, mul_inv_cancel_left, tr_mul]

theorem lineBaseChange_comp {B C₁ C : Type} [CommRing B] [Algebra 𝒪 B] [CommRing C₁] [Algebra 𝒪 C₁] [CommRing C] [Algebra 𝒪 C]
    (φ : B →ₐ[𝒪] C₁) (ψ : C₁ →ₐ[𝒪] C) (M : FullLattice 𝒪 K₀) (N : Submodule B (latticeBaseChange 𝒪 K₀ B M)) :
    lineBaseChange (ψ.comp φ) M N = lineBaseChange ψ M (lineBaseChange φ M N) := by
  rw [lineBaseChange, lineBaseChange, lineBaseChange, AlgHom.comp_toLinearMap, LinearMap.rTensor_comp,
    LinearMap.coe_comp, Set.image_comp]
  apply le_antisymm
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)
  · rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    induction hy using Submodule.span_induction with
    | mem s hs => exact Submodule.subset_span ⟨s, hs, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul b' a _ ha => rw [rTensor_smul_left]; exact Submodule.smul_mem _ _ ha

theorem lineBaseChange_eq_of_away {B : Type} [CommRing B] [Algebra 𝒪 B] (f : B) (M : FullLattice 𝒪 K₀)
    (N₁ N₂ : Submodule B (latticeBaseChange 𝒪 K₀ B M))
    (H : ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] [IsLocalization.Away f C],
      lineBaseChange (IsScalarTower.toAlgHom 𝒪 B C) M N₁ = lineBaseChange (IsScalarTower.toAlgHom 𝒪 B C) M N₂)
    (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] (hf : IsUnit (algebraMap B C f)) :
    lineBaseChange (IsScalarTower.toAlgHom 𝒪 B C) M N₁ = lineBaseChange (IsScalarTower.toAlgHom 𝒪 B C) M N₂ := by
  have H₁ := H (Localization.Away f)
  let ψ₀ : Localization.Away f →+* C := IsLocalization.Away.lift f hf
  have hψ₀ : ∀ b : B, ψ₀ (algebraMap B (Localization.Away f) b) = algebraMap B C b := fun b => IsLocalization.Away.lift_eq f hf b
  let ψ : Localization.Away f →ₐ[𝒪] C :=
    { toRingHom := ψ₀
      commutes' := fun o => by
        rw [IsScalarTower.algebraMap_apply 𝒪 B (Localization.Away f), IsScalarTower.algebraMap_apply 𝒪 B C]
        exact hψ₀ _ }
  have hcomp : IsScalarTower.toAlgHom 𝒪 B C = ψ.comp (IsScalarTower.toAlgHom 𝒪 B (Localization.Away f)) := by
    apply AlgHom.ext
    intro b
    exact (hψ₀ b).symm
  rw [hcomp, lineBaseChange_comp, lineBaseChange_comp, H₁]

end OverlapZar29

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
    Spec.map (CommRingCat.ofHom xq.toRingHom) ≫ M.ζ h n = Spec.map (CommRingCat.ofHom xq'.toRingHom) ≫ M.ζ h' n →
      ∃ (ι : Type) (_ : Finite ι) (f : ι → B), Ideal.span (Set.range f) = ⊤ ∧
        ∀ (i : ι) (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] [IsLocalization.Away (f i) C],
          ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧
            DeligneDatum.IsPullback (K := K₀) (π := π) C g⁻¹ ((Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B C) P)
              ((Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B C) P') := by
  haveI := hdvr
  intro n B _ _ h h' xq xq' d d' P P' hd hd' hP hP' heq

  obtain rfl : P = OverlapZar29.tr π h d := (OverlapZar29.isPullback_inv_iff π h d P).mp hP
  obtain rfl : P' = OverlapZar29.tr π h' d' := (OverlapZar29.isPullback_inv_iff π h' d' P').mp hP'
  refine Ideal.exists_finite_span_range_eq_top_of_forall_isPrime_exists_not_mem (P := (fun f : B => ∀ (C : Type) [CommRing C] [Algebra 𝒪 C] [Algebra B C] [IsScalarTower 𝒪 B C] [IsLocalization.Away f C],
      ∃ g : Matrix.GeneralLinearGroup (Fin 2) K₀, Matrix.ProjGenLinGroup.mk g ∈ N ∧
        DeligneDatum.IsPullback (K := K₀) (π := π) C g⁻¹ ((Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B C) (OverlapZar29.tr π h d))
          ((Omega K₀ π).map (IsScalarTower.toAlgHom 𝒪 B C) (OverlapZar29.tr π h' d')))) ?_
  intro 𝔭 h𝔭
  haveI := h𝔭

  let C𝔭 := Localization.AtPrime 𝔭
  let φ : B →ₐ[𝒪] C𝔭 := IsScalarTower.toAlgHom 𝒪 B C𝔭
  have heq𝔭 : Spec.map (CommRingCat.ofHom (φ.comp xq).toRingHom) ≫ M.ζ h n =
      Spec.map (CommRingCat.ofHom (φ.comp xq').toRingHom) ≫ M.ζ h' n := by
    have e1 : Spec.map (CommRingCat.ofHom (φ.comp xq).toRingHom) =
        Spec.map (CommRingCat.ofHom (algebraMap B C𝔭)) ≫ Spec.map (CommRingCat.ofHom xq.toRingHom) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl
    have e2 : Spec.map (CommRingCat.ofHom (φ.comp xq').toRingHom) =
        Spec.map (CommRingCat.ofHom (algebraMap B C𝔭)) ≫ Spec.map (CommRingCat.ofHom xq'.toRingHom) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl
    rw [e1, e2, Category.assoc, Category.assoc, heq]
  obtain ⟨g, hgN, hgP⟩ := (CerednikDrinfeld.FormalOmega.MumfordGlueCore.zeta_comp_eq_iff_exists_isPullback_of_isLocalRing
    𝒪 hdvr π hπ hres K₀ g₁ hg₁ N hN hNtype M n C𝔭 h h' (φ.comp xq) (φ.comp xq')
    ((Omega K₀ π).map φ d) ((Omega K₀ π).map φ d') ((Omega K₀ π).map φ (OverlapZar29.tr π h d)) ((Omega K₀ π).map φ (OverlapZar29.tr π h' d'))
    (ZetaRel29.ch_map 𝒪 π K₀ g₁ n φ xq d hd) (ZetaRel29.ch_map 𝒪 π K₀ g₁ n φ xq' d' hd')
    (ZetaRel29.isPullback_map π φ _ _ _ hP) (ZetaRel29.isPullback_map π φ _ _ _ hP')).mp heq𝔭

  set k : Matrix.GeneralLinearGroup (Fin 2) K₀ := h'⁻¹ * (g * h) with hk
  have E𝔭 : (Omega K₀ π).map φ d' = OverlapZar29.tr π k ((Omega K₀ π).map φ d) :=
    (OverlapZar29.isPullback_tr_iff π φ g h h' d d').mp hgP
  rw [← OverlapZar29.map_tr] at E𝔭
  have L : ∀ L₀ : FullLattice 𝒪 K₀, lineBaseChange φ L₀ ((OverlapZar29.tr π k d).line L₀) = lineBaseChange φ L₀ (d'.line L₀) := by
    intro L₀
    change ((Omega K₀ π).map φ (OverlapZar29.tr π k d)).line L₀ = ((Omega K₀ π).map φ d').line L₀
    rw [E𝔭]
  obtain ⟨f₁, hf₁, H₁⟩ := CerednikDrinfeld.FormalOmega.exists_not_mem_forall_lineBaseChange_eq_of_lineBaseChange_localization_eq
    (stdFullLattice K₀) ((OverlapZar29.tr π k d).line (stdFullLattice K₀)) (d'.line (stdFullLattice K₀))
    ((OverlapZar29.tr π k d).invertible _) (d'.invertible _) 𝔭 (L _)
  obtain ⟨f₂, hf₂, H₂⟩ := CerednikDrinfeld.FormalOmega.exists_not_mem_forall_lineBaseChange_eq_of_lineBaseChange_localization_eq
    (FullLattice.act g₁ (stdFullLattice K₀)) ((OverlapZar29.tr π k d).line _) (d'.line _)
    ((OverlapZar29.tr π k d).invertible _) (d'.invertible _) 𝔭 (L _)
  refine ⟨f₁ * f₂, fun hmem => (h𝔭.mem_or_mem hmem).elim hf₁ hf₂, ?_⟩
  intro C _ _ _ _ _

  have hu : IsUnit (algebraMap B C (f₁ * f₂)) := IsLocalization.Away.algebraMap_isUnit (f₁ * f₂)
  rw [map_mul] at hu
  have hu₁ : IsUnit (algebraMap B C f₁) := isUnit_of_mul_isUnit_left hu
  have hu₂ : IsUnit (algebraMap B C f₂) := isUnit_of_mul_isUnit_right hu
  let ψ : B →ₐ[𝒪] C := IsScalarTower.toAlgHom 𝒪 B C
  have K₁ := OverlapZar29.lineBaseChange_eq_of_away f₁ _ _ _ H₁ C hu₁
  have K₂ := OverlapZar29.lineBaseChange_eq_of_away f₂ _ _ _ H₂ C hu₂

  have hedge : ((Omega K₀ π).map ψ d').InEdgeChart π (FullLattice.act g₁ (stdFullLattice K₀)) (stdFullLattice K₀) :=
    ZetaRel29.inEdgeChart_map π ψ d' _ _ hd'.2.2
  have EC : (Omega K₀ π).map ψ (OverlapZar29.tr π k d) = (Omega K₀ π).map ψ d' :=
    CerednikDrinfeld.FormalOmega.DeligneDatum.eq_of_inEdgeChart_of_line_eq hπ _ _ _ _ hedge K₁ K₂
  refine ⟨g, hgN, (OverlapZar29.isPullback_tr_iff π ψ g h h' d d').mpr ?_⟩
  rw [← EC, OverlapZar29.map_tr]

end S_CerednikDrinfeld_FormalOmega_MumfordGlueCore_exists_finite_cover_isPullback_of_zeta_comp_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_MumfordGlueCore_exists_finite_cover_isPullback_of_zeta_comp_eq (solution)
