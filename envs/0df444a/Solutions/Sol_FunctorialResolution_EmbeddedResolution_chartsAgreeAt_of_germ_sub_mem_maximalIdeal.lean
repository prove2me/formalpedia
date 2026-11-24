-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.chartsAgreeAt_of_germ_sub_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:47:37.414196+00:00
-- url     : https://prove2.me/submissions/4b4071c4-04d6-4a20-8720-e5c7be78d4a5

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartFiberProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
section
variable {X : Scheme.{u}} {k : Type u} [Field k] {q : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}
end
section
variable {P : Scheme.{u}} {k : Type u} [Field k] {q : P ⟶ Spec (CommRingCat.of k)}
  {V : P.Opens} {n : ℕ}
private theorem appTop_comp_apply {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (x : C.presheaf.obj (op ⊤)) :
    (f ≫ g).appTop.hom x = f.appTop.hom (g.appTop.hom x) := rfl
private theorem affineSpaceFin_hom_ext {K : Type u} [Field K] {m : ℕ} {Z : Scheme.{u}}
    (f g : Z ⟶ affineSpaceFin K m)
    (h₁ : f ≫ affineSpaceFinToSpec K m = g ≫ affineSpaceFinToSpec K m)
    (h₂ : ∀ i : ULift.{u} (Fin m),
      f.appTop.hom (AffineSpace.coord (Spec (CommRingCat.of K)) i) =
        g.appTop.hom (AffineSpace.coord (Spec (CommRingCat.of K)) i)) :
    f = g := by
  apply AffineSpace.hom_ext
  · exact h₁
  · exact h₂
private theorem not_isUnit_of_mem_maximalIdeal {R : Type u} [CommRing R] [IsLocalRing R] {a : R}
    (ha : a ∈ IsLocalRing.maximalIdeal R) : ¬ IsUnit a :=
  (IsLocalRing.mem_maximalIdeal a).mp ha
private theorem specResidueField_eq_zero_of_not_isUnit {X : Scheme.{u}} (x : ↥X)
    (t : Γ(Spec (X.residueField x), ⊤)) (ht : ¬ IsUnit t) : t = 0 := by
  have h2 : (Scheme.ΓSpecIso (X.residueField x)).inv.hom
      ((Scheme.ΓSpecIso (X.residueField x)).hom.hom t) = t := by
    have e1 := congrArg CommRingCat.Hom.hom
      (Iso.hom_inv_id (Scheme.ΓSpecIso (X.residueField x)))
    rw [CommRingCat.hom_comp, CommRingCat.hom_id] at e1
    exact DFunLike.congr_fun e1 t
  by_contra hne
  have hne0 : (Scheme.ΓSpecIso (X.residueField x)).hom.hom t ≠ 0 := by
    intro h0
    apply hne
    rw [← h2, h0]
    exact map_zero _
  have hu : IsUnit ((Scheme.ΓSpecIso (X.residueField x)).hom.hom t) :=
    isUnit_iff_ne_zero.mpr hne0
  have hu2 : IsUnit ((Scheme.ΓSpecIso (X.residueField x)).inv.hom
      ((Scheme.ΓSpecIso (X.residueField x)).hom.hom t)) :=
    hu.map (Scheme.ΓSpecIso (X.residueField x)).inv.hom
  rw [h2] at hu2
  exact ht hu2
private theorem fromSpecResidueField_appTop_eq_zero {X : Scheme.{u}} (x : ↥X)
    (hx : x ∈ (⊤ : X.Opens)) (s : Γ(X, ⊤))
    (hs : (X.presheaf.germ ⊤ x hx).hom s ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x)) :
    (X.fromSpecResidueField x).appTop.hom s = 0 := by
  have hxb : x ∉ X.basicOpen s := fun hmem =>
    not_isUnit_of_mem_maximalIdeal hs ((X.mem_basicOpen_top s x).1 hmem)
  have hy : (X.fromSpecResidueField x).base (specResidueFieldPoint x) = x := by simp
  have hynot : specResidueFieldPoint x ∉ (Spec (X.residueField x)).basicOpen
      ((X.fromSpecResidueField x).appTop.hom s) := by
    intro hmem
    have h1 : specResidueFieldPoint x ∈ (X.fromSpecResidueField x) ⁻¹ᵁ (X.basicOpen s) := by
      rw [Scheme.preimage_basicOpen]
      exact hmem
    have h2 : (X.fromSpecResidueField x).base (specResidueFieldPoint x) ∈ X.basicOpen s := h1
    rw [hy] at h2
    exact hxb h2
  have hnu : ¬ IsUnit ((X.fromSpecResidueField x).appTop.hom s) := by
    intro hu
    apply hynot
    rw [Scheme.mem_basicOpen_top]
    exact hu.map
      ((Spec (X.residueField x)).presheaf.germ ⊤ (specResidueFieldPoint x) (by trivial)).hom
  exact specResidueField_eq_zero_of_not_isUnit x _ hnu
end
section
variable {P : Scheme.{u}} {k : Type u} [Field k] {q : P ⟶ Spec (CommRingCat.of k)}
  {V : P.Opens} {n : ℕ}
end
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {P : Scheme.{u}} {k : Type u} [Field k] {q : P ⟶ Spec (CommRingCat.of k)}
  {V : P.Opens} {n : ℕ}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (c₁ c₂ : EtaleChart q V n) (p : ↥P)
    (hp : p ∈ V)
    (h : ∀ j : Fin n,
      (V.toScheme.presheaf.germ ⊤ (pointOfMem V p hp) (by trivial)).hom
          (c₁.coordTop j - c₂.coordTop j) ∈
        IsLocalRing.maximalIdeal (V.toScheme.presheaf.stalk (pointOfMem V p hp))) :
    ChartsAgreeAt c₁ c₂ p hp := by
  have hover : (V.toScheme.fromSpecResidueField (pointOfMem V p hp) ≫ c₁.map) ≫
        affineSpaceFinToSpec k n =
      (V.toScheme.fromSpecResidueField (pointOfMem V p hp) ≫ c₂.map) ≫
        affineSpaceFinToSpec k n := by
    rw [Category.assoc, Category.assoc, c₁.comp_struct, c₂.comp_struct]
  refine affineSpaceFin_hom_ext _ _ hover ?_
  rintro ⟨j⟩
  have h0 := fromSpecResidueField_appTop_eq_zero (pointOfMem V p hp) (by trivial)
    (c₁.coordTop j - c₂.coordTop j) (h j)
  rw [map_sub, sub_eq_zero] at h0
  rw [appTop_comp_apply, appTop_comp_apply]
  exact h0
end FunctorialResolution.EmbeddedResolution
