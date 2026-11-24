-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.stalkIdeal_eq_map_germ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:02.318803+00:00
-- url     : https://prove2.me/submissions/139f4d8f-22bb-46d4-aacd-fe690a8ec349

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_AffineOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealSheafOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace FunctorialResolution.EmbeddedResolution
open AlgebraicGeometry TopologicalSpace
universe u
variable {X : Scheme.{u}}
private theorem map_germ_ideal_congr {X : Scheme.{u}} (I : X.IdealSheafData) (x : X)
    (W W' : X.affineOpens) (h : W = W') (hW : x ∈ W.1) (hW' : x ∈ W'.1) :
    Ideal.map (X.presheaf.germ W.1 x hW).hom (I.ideal W)
      = Ideal.map (X.presheaf.germ W'.1 x hW').hom (I.ideal W') := by
  subst h
  rfl
open CategoryTheory in
private theorem map_germ_ideal_affineBasicOpen {X : Scheme.{u}} (I : X.IdealSheafData) (x : X)
    (U : X.affineOpens) (f : Γ(X, U.1)) (hxU : x ∈ U.1)
    (hxf : x ∈ (X.affineBasicOpen f).1) :
    Ideal.map (X.presheaf.germ U.1 x hxU).hom (I.ideal U)
      = Ideal.map (X.presheaf.germ (X.affineBasicOpen f).1 x hxf).hom
          (I.ideal (X.affineBasicOpen f)) := by
  have hxf' : x ∈ X.basicOpen f := hxf
  have hgerm : (X.presheaf.germ (X.basicOpen f) x hxf').hom.comp
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
      = (X.presheaf.germ U.1 x hxU).hom := by
    rw [← CommRingCat.hom_comp, X.presheaf.germ_res]
  have h1 : Ideal.map (X.presheaf.germ (X.basicOpen f) x hxf').hom
      (Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom (I.ideal U))
      = Ideal.map (X.presheaf.germ U.1 x hxU).hom (I.ideal U) := by
    rw [Ideal.map_map, hgerm]
  rw [← h1]
  exact congrArg (fun J : Ideal Γ(X, X.basicOpen f) =>
    Ideal.map (X.presheaf.germ (X.basicOpen f) x hxf').hom J) (I.map_ideal_basicOpen U f)
private theorem map_germ_ideal_eq {X : Scheme.{u}} (I : X.IdealSheafData) (x : X)
    (V U : X.affineOpens) (hxV : x ∈ V.1) (hxU : x ∈ U.1) :
    Ideal.map (X.presheaf.germ V.1 x hxV).hom (I.ideal V)
      = Ideal.map (X.presheaf.germ U.1 x hxU).hom (I.ideal U) := by
  obtain ⟨f, g, hfg, hxf⟩ :=
    AlgebraicGeometry.exists_basicOpen_le_affine_inter V.2 U.2 x ⟨hxV, hxU⟩
  have hxg : x ∈ X.basicOpen g := by rw [← hfg]; exact hxf
  have hW : X.affineBasicOpen f = X.affineBasicOpen g := Subtype.ext hfg
  rw [map_germ_ideal_affineBasicOpen I x V f hxV hxf,
    map_germ_ideal_affineBasicOpen I x U g hxU hxg]
  exact map_germ_ideal_congr I x (X.affineBasicOpen f) (X.affineBasicOpen g) hW hxf hxg
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open AlgebraicGeometry TopologicalSpace
universe u
variable {X : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (I : X.IdealSheafData) (x : X) (U : X.affineOpens)
    (hx : x ∈ U.1) :
    stalkIdeal I x = Ideal.map (X.presheaf.germ U.1 x hx).hom (I.ideal U) := by
  have h : stalkIdeal I x = ⨆ V : {V : X.affineOpens // x ∈ V.1.1},
      Ideal.map (X.presheaf.germ V.1.1 x V.2).hom (I.ideal V.1) := rfl
  rw [h]
  refine le_antisymm (iSup_le ?_) ?_
  · rintro ⟨V, hxV⟩
    exact le_of_eq (map_germ_ideal_eq I x V U hxV hx)
  · exact le_iSup (fun V : {V : X.affineOpens // x ∈ V.1.1} =>
      Ideal.map (X.presheaf.germ V.1.1 x V.2).hom (I.ideal V.1)) ⟨U, hx⟩
end FunctorialResolution.EmbeddedResolution
