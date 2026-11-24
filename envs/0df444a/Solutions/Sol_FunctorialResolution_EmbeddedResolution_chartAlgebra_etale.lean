-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.chartAlgebra_etale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:47:33.613466+00:00
-- url     : https://prove2.me/submissions/60a0f19e-7f82-427a-8df1-9a277b91e09b

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace FunctorialResolution.EmbeddedResolution
variable {X Y : Scheme.{u}} {W : X.Opens} {V : Y.Opens} {n : Type u}
private theorem algebraEtale_congr {R S : Type u} [CommRing R] [CommRing S] {f f' : R →+* S}
    (h : f = f') (hf : @Algebra.Etale R S _ _ f.toAlgebra) :
    @Algebra.Etale R S _ _ f'.toAlgebra := by
  subst h
  exact hf
private theorem algebraEtale_of_ringHomEtale {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (h : RingHom.Etale f) : @Algebra.Etale R S _ _ f.toAlgebra := h
private theorem algebraEtale_comp_equiv {R R' S S' : Type u} [CommRing R] [CommRing R']
    [CommRing S] [CommRing S'] (eR : R' ≃+* R) (f : R →+* S) (eS : S ≃+* S')
    (hf : @Algebra.Etale R S _ _ f.toAlgebra) :
    @Algebra.Etale R' S' _ _ (((eS : S →+* S').comp (f.comp (eR : R' →+* R))).toAlgebra) := by
  let : Algebra R S := f.toAlgebra
  have : Algebra.Etale R S := hf
  let : Algebra R' R := (eR : R' →+* R).toAlgebra
  let : Algebra R S' := ((eS : S →+* S').comp f).toAlgebra
  let : Algebra R' S' := ((eS : S →+* S').comp (f.comp (eR : R' →+* R))).toAlgebra
  have : IsScalarTower R' R S' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.Etale R' R' := inferInstance
  have : Algebra.Etale R' R :=
    Algebra.Etale.of_equiv (R := R') (A := R') (AlgEquiv.ofRingEquiv (f := eR) fun _ => rfl)
  have : Algebra.Etale R S' :=
    Algebra.Etale.of_equiv (R := R) (A := S) (AlgEquiv.ofRingEquiv (f := eS) fun _ => rfl)
  exact Algebra.Etale.comp R' R S'
private theorem comp_appTop_apply {A B C : Scheme.{u}} (f : A ⟶ B) (k : B ⟶ C) (z : Γ(C, ⊤)) :
    (f ≫ k).appTop.hom z = f.appTop.hom (k.appTop.hom z) :=
  congrArg (fun m : Γ(C, ⊤) ⟶ Γ(A, ⊤) => CommRingCat.Hom.hom m z) (Scheme.Hom.comp_appTop f k)
private theorem specMap_appTop_apply {R S : CommRingCat.{u}} (u : R ⟶ S) (a : R) :
    (Spec.map u).appTop.hom ((Scheme.ΓSpecIso R).inv.hom a) =
      (Scheme.ΓSpecIso S).inv.hom (u.hom a) :=
  (congrArg (fun m : R ⟶ Γ(Spec S, ⊤) => CommRingCat.Hom.hom m a)
    (Scheme.ΓSpecIso_inv_naturality u)).symm
private theorem isoSpec_hom_appTop_apply (Z : Scheme.{u}) [IsAffine Z] (a : Γ(Z, ⊤)) :
    Z.isoSpec.hom.appTop.hom ((Scheme.ΓSpecIso Γ(Z, ⊤)).inv.hom a) = a := by
  rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
  exact congrArg (fun m : Γ(Z, ⊤) ⟶ Γ(Z, ⊤) => CommRingCat.Hom.hom m a)
    (Scheme.ΓSpecIso Γ(Z, ⊤)).inv_hom_id
private theorem affineOpenIsoSpec_hom_appTop_apply {X' : Scheme.{u}} {W' : X'.Opens}
    (hW : IsAffineOpen W') (a : Γ(X', W')) :
    (affineOpenIsoSpec hW).hom.appTop.hom ((Scheme.ΓSpecIso Γ(X', W')).inv.hom a) =
      W'.topIso.inv.hom a := by
  have : IsAffine W'.toScheme := hW
  show (W'.toScheme.isoSpec.hom ≫ Spec.map W'.topIso.symm.hom).appTop.hom
      ((Scheme.ΓSpecIso Γ(X', W')).inv.hom a) = W'.topIso.inv.hom a
  rw [comp_appTop_apply, specMap_appTop_apply, isoSpec_hom_appTop_apply]
  rfl
private theorem affineSpaceOpenIsoSpecMvPolynomial_hom_appTop_X {X' : Scheme.{u}} {W' : X'.Opens} (hW : IsAffineOpen W')
    (m : Type u) (j : m) :
    (affineSpaceOpenIsoSpecMvPolynomial hW m).hom.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial m Γ(X', W')))).inv.hom
          (MvPolynomial.X j)) =
      AffineSpace.coord W'.toScheme j := by
  have key : (AffineSpace.SpecIso m Γ(X', W')).hom.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial m Γ(X', W')))).inv.hom
        (MvPolynomial.X j)) = AffineSpace.coord (Spec Γ(X', W')) j := by
    rw [← AffineSpace.SpecIso_inv_appTop_coord, ← comp_appTop_apply, Iso.hom_inv_id]
    simp
  show ((AffineSpace.map m (affineOpenIsoSpec hW).hom) ≫
      (AffineSpace.SpecIso m Γ(X', W')).hom).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial m Γ(X', W')))).inv.hom
        (MvPolynomial.X j)) = AffineSpace.coord W'.toScheme j
  rw [comp_appTop_apply, key, AffineSpace.map_appTop_coord]
private theorem affineSpaceOpenIsoSpecMvPolynomial_hom_appTop_C {X' : Scheme.{u}} {W' : X'.Opens} (hW : IsAffineOpen W')
    (m : Type u) (a : Γ(X', W')) :
    (affineSpaceOpenIsoSpecMvPolynomial hW m).hom.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial m Γ(X', W')))).inv.hom
          (MvPolynomial.C a)) =
      (AffineSpace m W'.toScheme ↘ W'.toScheme).appTop.hom (W'.topIso.inv.hom a) := by
  have h1 : (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : Γ(X', W') →+* MvPolynomial m Γ(X', W')))).appTop.hom
        ((Scheme.ΓSpecIso Γ(X', W')).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial m Γ(X', W')))).inv.hom
        (MvPolynomial.C a) :=
    specMap_appTop_apply _ a
  have key : (AffineSpace.SpecIso m Γ(X', W')).hom.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial m Γ(X', W')))).inv.hom
        (MvPolynomial.C a)) =
      (AffineSpace m (Spec Γ(X', W')) ↘ Spec Γ(X', W')).appTop.hom
        ((Scheme.ΓSpecIso Γ(X', W')).inv.hom a) := by
    rw [← h1, ← comp_appTop_apply, ← AffineSpace.SpecIso_inv_over, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp]
  show ((AffineSpace.map m (affineOpenIsoSpec hW).hom) ≫
      (AffineSpace.SpecIso m Γ(X', W')).hom).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial m Γ(X', W')))).inv.hom
        (MvPolynomial.C a)) =
      (AffineSpace m W'.toScheme ↘ W'.toScheme).appTop.hom (W'.topIso.inv.hom a)
  rw [comp_appTop_apply, key, ← comp_appTop_apply, AffineSpace.map_over, comp_appTop_apply,
    affineOpenIsoSpec_hom_appTop_apply]
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X Y : Scheme.{u}} {W : X.Opens} {V : Y.Opens} {n : Type u}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (hW : IsAffineOpen W) (hV : IsAffineOpen V)
    (g : V.toScheme ⟶ AffineSpace n W.toScheme) [Etale g] :
    letI : Algebra (MvPolynomial n Γ(X, W)) Γ(Y, V) := chartAlgebra hW g
    Algebra.Etale (MvPolynomial n Γ(X, W)) Γ(Y, V) := by
  let : Algebra (MvPolynomial n Γ(X, W)) Γ(Y, V) := chartAlgebra hW g
  have : IsAffine V.toScheme := hV
  have : IsAffine W.toScheme := hW
  have hEt : Etale (g ≫ (affineSpaceOpenIsoSpecMvPolynomial hW n).hom) := inferInstance
  have hr : RingHom.Etale (g ≫ (affineSpaceOpenIsoSpecMvPolynomial hW n).hom).appTop.hom :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp hEt
  have hAlg := algebraEtale_of_ringHomEtale _ hr
  have h2 := algebraEtale_comp_equiv
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial n Γ(X, W)))).symm.commRingCatIsoToRingEquiv
    (g ≫ (affineSpaceOpenIsoSpecMvPolynomial hW n).hom).appTop.hom V.topIso.commRingCatIsoToRingEquiv hAlg
  refine algebraEtale_congr ?_ h2
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
  · have hC : chartEvalHom hW g (MvPolynomial.C a) = chartCoeffHom g a := by simp [chartEvalHom]
    show V.topIso.hom.hom ((g ≫ (affineSpaceOpenIsoSpecMvPolynomial hW n).hom).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial n Γ(X, W)))).inv.hom
          (MvPolynomial.C a))) = chartEvalHom hW g (MvPolynomial.C a)
    rw [comp_appTop_apply, affineSpaceOpenIsoSpecMvPolynomial_hom_appTop_C, ← comp_appTop_apply, hC]
    rfl
  · show V.topIso.hom.hom ((g ≫ (affineSpaceOpenIsoSpecMvPolynomial hW n).hom).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial n Γ(X, W)))).inv.hom
          (MvPolynomial.X j))) = chartEvalHom hW g (MvPolynomial.X j)
    rw [comp_appTop_apply, affineSpaceOpenIsoSpecMvPolynomial_hom_appTop_X]
    simp [chartEvalHom, chartVar]
end FunctorialResolution.EmbeddedResolution
