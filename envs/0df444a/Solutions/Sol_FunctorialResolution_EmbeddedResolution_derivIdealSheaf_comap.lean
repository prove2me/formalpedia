-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.derivIdealSheaf_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:59:11.586802+00:00
-- url     : https://prove2.me/submissions/eae3ded9-92a3-4951-b372-15bcf775b3da

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartAlgebra
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_PolynomialCoordinateExtension
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothEtaleChart
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealEtaleBaseChange
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheafSmoothPullback
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_sectionsAlgebraMap_appLE_apply
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_ideal_eq_map_appLE
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_algebra_formallyEtale
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coord_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_isScalarTower
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_X_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_algebraMap_X_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_coord_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_formallyEtale_trans
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_map_derivIdeal_sum
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_sumEvalAlgebra_isScalarTower
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_HasStrictNormalCrossingsWith_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_InStrictNormalCrossingPositionAt_exists_etaleChart
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SmoothEtaleChart_exists_isAffineOpen_etale_resLE_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_chartAlgebra_formallyEtale
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_chartAlgebra_isScalarTower
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_etaleChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.coordRingHom_X
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.algebraMap_X_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.algebraMap_X_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.coord_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.coord_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal


section
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FunctorialResolution.EmbeddedResolution
private theorem exists_pow_mul_mem_of_mem_map {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (f : R) [IsLocalization.Away f S] (N : Ideal R) (x : R)
    (hx : algebraMap R S x ∈ N.map (algebraMap R S)) : ∃ n : ℕ, f ^ n * x ∈ N := by
  obtain ⟨⟨a, t⟩, hmul⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (M := Submonoid.powers f) (S := S)).mp hx
  have hmul' : algebraMap R S (x * (t : R)) = algebraMap R S (a : R) := by
    rw [map_mul]
    exact hmul
  obtain ⟨c, hceq⟩ :=
    (IsLocalization.eq_iff_exists (M := Submonoid.powers f) (S := S)).mp hmul'
  obtain ⟨i, hi⟩ := t.2
  obtain ⟨j, hj⟩ := c.2
  have hi' : f ^ i = (t : R) := hi
  have hj' : f ^ j = (c : R) := hj
  refine ⟨i + j, ?_⟩
  have key : f ^ (i + j) * x = f ^ j * (x * f ^ i) := by ring
  rw [key, hi', hj', hceq]
  exact N.mul_mem_left _ a.2
private theorem idealSheafData_ideal_le_congr {Y : Scheme.{u}} (J₁ J₂ : Y.IdealSheafData)
    {A B : Y.affineOpens} (hAB : A = B) (h : J₁.ideal B ≤ J₂.ideal B) :
    J₁.ideal A ≤ J₂.ideal A := by
  subst hAB
  exact h
private theorem idealSheafData_ideal_le_of_locally_le {Y : Scheme.{u}} (J₁ J₂ : Y.IdealSheafData)
    (H : ∀ y : Y, ∃ (V : Y.Opens) (hV : IsAffineOpen V), y ∈ V ∧
      J₁.ideal ⟨V, hV⟩ ≤ J₂.ideal ⟨V, hV⟩) (U : Y.affineOpens) :
    J₁.ideal U ≤ J₂.ideal U := by
  intro x hx
  set s : Set Γ(Y, U.1) := {f : Γ(Y, U.1) | ∃ n : ℕ, f ^ n * x ∈ J₂.ideal U} with hs
  have hcover : U.1 ≤ ⨆ f : s, Y.basicOpen (f : Γ(Y, U.1)) := by
    intro z hz
    obtain ⟨V, hV, hzV, hle⟩ := H z
    obtain ⟨f, g, hfg, hzf⟩ := exists_basicOpen_le_affine_inter U.2 hV z ⟨hz, hzV⟩
    have hres : Ideal.map (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom (J₁.ideal U)
        ≤ Ideal.map (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom (J₂.ideal U) := by
      rw [J₁.map_ideal_basicOpen U f, J₂.map_ideal_basicOpen U f]
      have hABO : Y.affineBasicOpen f = Y.affineBasicOpen (U := ⟨V, hV⟩) g := Subtype.ext hfg
      refine idealSheafData_ideal_le_congr J₁ J₂ hABO ?_
      rw [← J₁.map_ideal_basicOpen ⟨V, hV⟩ g, ← J₂.map_ideal_basicOpen ⟨V, hV⟩ g]
      exact Ideal.map_mono hle
    have hfs : f ∈ s := by
      have := U.2.isLocalization_basicOpen f
      rw [hs]
      refine exists_pow_mul_mem_of_mem_map (S := Γ(Y, Y.basicOpen f)) f (J₂.ideal U) x ?_
      have halg : (algebraMap Γ(Y, U.1) Γ(Y, Y.basicOpen f))
          = (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op).hom := rfl
      rw [halg]
      exact hres (Ideal.mem_map_of_mem _ hx)
    exact Opens.mem_iSup.mpr ⟨⟨f, hfs⟩, hzf⟩
  have hspan : Ideal.span s = ⊤ := (U.2.self_le_iSup_basicOpen_iff).mp hcover
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem (J₂.ideal U) s hspan x ?_
  rintro ⟨f, hf⟩
  rw [hs] at hf
  obtain ⟨n, hn⟩ := hf
  exact ⟨n, by rw [smul_eq_mul]; exact hn⟩
private theorem idealSheafData_eq_of_locally_eq {Y : Scheme.{u}} (J₁ J₂ : Y.IdealSheafData)
    (H : ∀ y : Y, ∃ (V : Y.Opens) (hV : IsAffineOpen V), y ∈ V ∧
      J₁.ideal ⟨V, hV⟩ = J₂.ideal ⟨V, hV⟩) : J₁ = J₂ := by
  have key : ∀ U : Y.affineOpens, J₁.ideal U = J₂.ideal U := by
    intro U
    refine le_antisymm (idealSheafData_ideal_le_of_locally_le J₁ J₂ ?_ U)
      (idealSheafData_ideal_le_of_locally_le J₂ J₁ ?_ U)
    · intro y
      obtain ⟨V, hV, h1, h2⟩ := H y
      exact ⟨V, hV, h1, h2.le⟩
    · intro y
      obtain ⟨V, hV, h1, h2⟩ := H y
      exact ⟨V, hV, h1, h2.ge⟩
  exact Scheme.IdealSheafData.ext (funext key)
attribute [local instance] EtaleCoordinates.sumEvalAlgebra in
private theorem exists_affineOpen_derivIdealSheaf_comap_ideal_eq (k : Type u) [Field k] [IsNoetherianRing k]
    {X Y : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p]
    (h : Y ⟶ X) [Smooth h] [LocallyOfFiniteType (h ≫ p)] (I : X.IdealSheafData) (y : Y) :
    ∃ (V : Y.Opens) (hV : IsAffineOpen V), y ∈ V ∧
      (derivIdealSheaf k (h ≫ p) (I.comap h)).ideal ⟨V, hV⟩
        = ((derivIdealSheaf k p I).comap h).ideal ⟨V, hV⟩ := by
  classical
  obtain ⟨W₀, m, hxW₀, -, ⟨c₀⟩⟩ := exists_etaleChart p (h.base y)
  obtain ⟨W, V, d, e, hW, hV, hyV, hWW₀, -, g, hgE, hg⟩ :=
    SmoothEtaleChart.exists_isAffineOpen_etale_resLE_le h y W₀ hxW₀ ⊤ (by trivial)
  refine ⟨V, hV, hyV, ?_⟩
  have : Etale g := hgE
  let c : EtaleChart p W m := c₀.restrict hWW₀
  let instkS : Algebra k Γ(X, W) := sectionsAlgebra k p W
  let instkT : Algebra k Γ(Y, V) := sectionsAlgebra k (h ≫ p) V
  let instPS : Algebra (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, W) := c.algebra
  let instTow1 : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, W) := c.isScalarTower
  have instFE1 : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin m)) k) Γ(X, W) :=
    c.algebra_formallyEtale hW
  let instChartAlgebra : Algebra (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V) := chartAlgebra hW g
  have instFE2 : Algebra.FormallyEtale (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V) :=
    chartAlgebra_formallyEtale hW hV g
  let instST : Algebra Γ(X, W) Γ(Y, V) := (h.appLE W V e).hom.toAlgebra
  let instTowkST : IsScalarTower k Γ(X, W) Γ(Y, V) :=
    IsScalarTower.of_algebraMap_eq fun a => (sectionsAlgebraMap_appLE_apply k p h W V e a).symm
  let instScalarTowerChart : IsScalarTower Γ(X, W) (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V) :=
    chartAlgebra_isScalarTower hW h e g hg
  let instSumT : Algebra (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) Γ(Y, V) :=
    ((algebraMap (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V)).comp
      (algebraMap (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
        (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)))).toAlgebra
  let instScalarTowerSum : IsScalarTower (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
      (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have instTowkSum : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
      Γ(Y, V) := by
    have : IsScalarTower k (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
        (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) :=
      EtaleCoordinates.sumEvalAlgebra_isScalarTower k (ULift.{u} (Fin m)) (ULift.{u} (Fin d))
        Γ(X, W)
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    rw [IsScalarTower.algebraMap_apply (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
        (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V)
        (algebraMap k (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) a),
      ← IsScalarTower.algebraMap_apply k (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
        (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) a,
      IsScalarTower.algebraMap_apply k Γ(X, W) (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) a,
      ← IsScalarTower.algebraMap_apply Γ(X, W) (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V),
      ← IsScalarTower.algebraMap_apply k Γ(X, W) Γ(Y, V)]
  have instFE3 : Algebra.FormallyEtale
      (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k) Γ(Y, V) :=
    EtaleCoordinates.formallyEtale_trans k (ULift.{u} (Fin m)) (ULift.{u} (Fin d))
      Γ(X, W) Γ(Y, V)
  have hcoord : ∀ i : ULift.{u} (Fin m),
      algebraMap Γ(X, W) Γ(Y, V) (EtaleCoordinates.coord k (ULift.{u} (Fin m)) Γ(X, W) i)
        = EtaleCoordinates.coord k (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) Γ(Y, V)
            (Sum.inl i) := by
    intro i
    rw [EtaleCoordinates.coord_def k (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) Γ(Y, V) (Sum.inl i),
      IsScalarTower.algebraMap_apply (MvPolynomial (ULift.{u} (Fin m) ⊕ ULift.{u} (Fin d)) k)
        (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V),
      EtaleCoordinates.algebraMap_X_inl k (ULift.{u} (Fin m)) (ULift.{u} (Fin d)) Γ(X, W),
      ← MvPolynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply Γ(X, W) (MvPolynomial (ULift.{u} (Fin d)) Γ(X, W)) Γ(Y, V)]
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE (derivIdealSheaf k p I) h ⟨W, hW⟩ ⟨V, hV⟩ e]
  simp only [derivIdealSheaf_ideal]
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE I h ⟨W, hW⟩ ⟨V, hV⟩ e]
  exact (EtaleCoordinates.map_derivIdeal_sum k (ULift.{u} (Fin m)) (ULift.{u} (Fin d))
    Γ(X, W) Γ(Y, V) hcoord (I.ideal ⟨W, hW⟩)).symm
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type u) [Field k] [IsNoetherianRing k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [Smooth p] [LocallyOfFiniteType p]
    (h : Y ⟶ X) [Smooth h] [LocallyOfFiniteType (h ≫ p)] (I : X.IdealSheafData) :
    derivIdealSheaf k (h ≫ p) (I.comap h) = (derivIdealSheaf k p I).comap h :=
  idealSheafData_eq_of_locally_eq _ _ fun y => exists_affineOpen_derivIdealSheaf_comap_ideal_eq k p h I y
end FunctorialResolution.EmbeddedResolution
