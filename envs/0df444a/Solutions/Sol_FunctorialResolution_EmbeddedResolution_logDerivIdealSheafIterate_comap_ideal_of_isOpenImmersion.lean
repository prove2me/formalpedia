-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.logDerivIdealSheafIterate_comap_ideal_of_isOpenImmersion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:01:30.84618+00:00
-- url     : https://prove2.me/submissions/c0f20172-04d1-4d9c-869b-90dd53a5c247

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealLocalization
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdealSheafOpenImmersion
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_algebraMap_sectionsAlgebra
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdealIterate_map_away
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdealSheafIterate_ideal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.logDerivIdealSheafIterate_ideal


section
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace FunctorialResolution.EmbeddedResolution
private theorem bijective_hom_of_iso {A B : CommRingCat.{u}} (i : A ≅ B) :
    Function.Bijective i.hom.hom :=
  ConcreteCategory.bijective_of_isIso i.hom
private theorem map_eq_comap_of_inverse {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (ψ : B →+* A) (h1 : ∀ a, ψ (φ a) = a) (h2 : ∀ b, φ (ψ b) = b) (J : Ideal A) :
    Ideal.map φ J = Ideal.comap ψ J := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, h1]
    exact ha
  · intro x hx
    rw [Ideal.mem_comap] at hx
    have hmem := Ideal.mem_map_of_mem φ hx
    rwa [h2 x] at hmem
private theorem ideal_comap_eq_map_appLE {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] (V : X.affineOpens) (hU : IsAffineOpen (f ''ᵁ (V : X.Opens)))
    (e : (V : X.Opens) ≤ f ⁻¹ᵁ (f ''ᵁ (V : X.Opens))) :
    (I.comap f).ideal V =
      (I.ideal ⟨f ''ᵁ (V : X.Opens), hU⟩).map
        (f.appLE (f ''ᵁ (V : X.Opens)) (V : X.Opens) e).hom := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion I f V]
  have happ : f.appLE (f ''ᵁ (V : X.Opens)) (V : X.Opens) e = (f.appIso (V : X.Opens)).hom :=
    (Scheme.Hom.appIso_hom' f (V : X.Opens)).symm
  rw [happ]
  have h1 : ∀ a, (f.appIso (V : X.Opens)).inv.hom ((f.appIso (V : X.Opens)).hom.hom a) = a :=
    fun a => CommRingCat.inv_hom_apply (f.appIso (V : X.Opens)) a
  have h2 : ∀ b, (f.appIso (V : X.Opens)).hom.hom ((f.appIso (V : X.Opens)).inv.hom b) = b :=
    fun b => CommRingCat.hom_inv_apply (f.appIso (V : X.Opens)) b
  exact (map_eq_comap_of_inverse _ _ h1 h2 _).symm
private theorem bijective_appLE_image_of_isOpenImmersion {Z W : Scheme.{u}} (f : W ⟶ Z) [IsOpenImmersion f]
    (V : W.Opens) (e : V ≤ f ⁻¹ᵁ (f ''ᵁ V)) :
    Function.Bijective (f.appLE (f ''ᵁ V) V e).hom := by
  have h : f.appLE (f ''ᵁ V) V e = (f.appIso V).hom := (Scheme.Hom.appIso_hom' f V).symm
  rw [h]
  exact bijective_hom_of_iso (f.appIso V)
private theorem appLE_sectionsAlgebraMap (K : Type u) [CommRing K] {Z W : Scheme.{u}}
    (q : Z ⟶ Spec (CommRingCat.of K)) (f : W ⟶ Z) (U : Z.Opens) (V : W.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (a : K) :
    (f.appLE U V e).hom (sectionsAlgebraMap K q U a) = sectionsAlgebraMap K (f ≫ q) V a := by
  have key : (f.appLE U V e).hom.comp (sectionsAlgebraMap K q U)
      = sectionsAlgebraMap K (f ≫ q) V := by
    rw [sectionsAlgebraMap_eq, sectionsAlgebraMap_eq, ← CommRingCat.hom_comp, Category.assoc,
      Scheme.Hom.appLE_comp_appLE]
  exact DFunLike.congr_fun key a
private theorem map_logDerivIdealIterate_of_bijective (K : Type u) [CommRing K]
    {S S' : Type u} [CommRing S] [CommRing S'] [Algebra K S] [Algebra K S']
    (φ : S →+* S') (hφ : Function.Bijective φ)
    (hcomp : ∀ a : K, φ (algebraMap K S a) = algebraMap K S' a)
    [Module.FinitePresentation S Ω[S⁄K]]
    {P : Ideal S} (hP : P.FG) (r : ℕ) (J : Ideal S) :
    Ideal.map φ (logDerivIdealIterate K P r J) =
      logDerivIdealIterate K (Ideal.map φ P) r (Ideal.map φ J) := by
  let _ : Algebra S S' := φ.toAlgebra
  have : IsScalarTower K S S' := IsScalarTower.of_algebraMap_eq fun a => (hcomp a).symm
  have : IsLocalization.Away (1 : S) S' :=
    IsLocalization.away_of_isUnit_of_bijective (hr := isUnit_one) (H := hφ)
  exact logDerivIdealIterate_map_away K (1 : S) hP r J
private theorem map_appLE_logDerivIdealIterate_of_bijective (K : Type u) [CommRing K] [IsNoetherianRing K]
    {Z W : Scheme.{u}} (q : Z ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType q]
    (f : W ⟶ Z) [LocallyOfFiniteType (f ≫ q)]
    (U : Z.affineOpens) (V : W.affineOpens) (e : (V : W.Opens) ≤ f ⁻¹ᵁ (U : Z.Opens))
    (hbij : Function.Bijective (f.appLE (U : Z.Opens) (V : W.Opens) e).hom)
    (P A : Ideal Γ(Z, (U : Z.Opens))) (r : ℕ) :
    Ideal.map (f.appLE (U : Z.Opens) (V : W.Opens) e).hom
        (@logDerivIdealIterate K _ _ _ (sectionsAlgebra K q (U : Z.Opens)) P r A) =
      @logDerivIdealIterate K _ _ _ (sectionsAlgebra K (f ≫ q) (V : W.Opens))
        (Ideal.map (f.appLE (U : Z.Opens) (V : W.Opens) e).hom P) r
        (Ideal.map (f.appLE (U : Z.Opens) (V : W.Opens) e).hom A) := by
  have hfp := @finitePresentation_kaehlerDifferential_sections K _ _ Z q _ U
    (sectionsAlgebra K q (U : Z.Opens)) (algebraMap_sectionsAlgebra K q (U : Z.Opens))
  have hno := @isNoetherianRing_sections K _ _ Z q _ U
    (sectionsAlgebra K q (U : Z.Opens)) (algebraMap_sectionsAlgebra K q (U : Z.Opens))
  have hP : P.FG := IsNoetherian.noetherian P
  have hcomp : ∀ a : K, (f.appLE (U : Z.Opens) (V : W.Opens) e).hom
      (@algebraMap K Γ(Z, (U : Z.Opens)) _ _ (sectionsAlgebra K q (U : Z.Opens)) a) =
      @algebraMap K Γ(W, (V : W.Opens)) _ _ (sectionsAlgebra K (f ≫ q) (V : W.Opens)) a := by
    intro a
    rw [algebraMap_sectionsAlgebra, algebraMap_sectionsAlgebra]
    exact appLE_sectionsAlgebraMap K q f (U : Z.Opens) (V : W.Opens) e a
  exact @map_logDerivIdealIterate_of_bijective K _ Γ(Z, (U : Z.Opens)) Γ(W, (V : W.Opens)) _ _
    (sectionsAlgebra K q (U : Z.Opens)) (sectionsAlgebra K (f ≫ q) (V : W.Opens))
    (f.appLE (U : Z.Opens) (V : W.Opens) e).hom hbij hcomp hfp P hP r A
variable (k : Type u) [CommRing k] [IsNoetherianRing k] {X Y : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
  (g : Y ⟶ X) [IsOpenImmersion g] [LocallyOfFiniteType (g ≫ p)]
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k : Type u) [CommRing k] [IsNoetherianRing k] {X Y : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
  (g : Y ⟶ X) [IsOpenImmersion g] [LocallyOfFiniteType (g ≫ p)]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution
    (P A : X.IdealSheafData) (r : ℕ) (V : Y.affineOpens) :
    ((logDerivIdealSheafIterate k p P r A).comap g).ideal V =
      (logDerivIdealSheafIterate k (g ≫ p) (P.comap g) r (A.comap g)).ideal V := by
  have hU : IsAffineOpen (g ''ᵁ (V : Y.Opens)) := V.2.image_of_isOpenImmersion g
  have e : (V : Y.Opens) ≤ g ⁻¹ᵁ (g ''ᵁ (V : Y.Opens)) := by
    intro x hx
    exact ⟨x, hx, rfl⟩
  have hbij : Function.Bijective
      (g.appLE (g ''ᵁ (V : Y.Opens)) (V : Y.Opens) e).hom :=
    bijective_appLE_image_of_isOpenImmersion g (V : Y.Opens) e
  rw [ideal_comap_eq_map_appLE _ g V hU e, logDerivIdealSheafIterate_ideal,
    logDerivIdealSheafIterate_ideal, ideal_comap_eq_map_appLE P g V hU e,
    ideal_comap_eq_map_appLE A g V hU e]
  exact map_appLE_logDerivIdealIterate_of_bijective k p g ⟨g ''ᵁ (V : Y.Opens), hU⟩ V e hbij _ _ r
end FunctorialResolution.EmbeddedResolution
