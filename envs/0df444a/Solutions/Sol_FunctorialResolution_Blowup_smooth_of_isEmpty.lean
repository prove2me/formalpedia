-- Prove2me | solution 1 for FunctorialResolution.Blowup.smooth_of_isEmpty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:46:33.122925+00:00
-- url     : https://prove2.me/submissions/426f8254-d77e-4d09-a2e1-dd741ae1bfef

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupOpenCover
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_SchemeCoproduct
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupCoproduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
namespace FunctorialResolution.Blowup
private theorem subsingleton_presheaf_of_isEmpty {X : Scheme.{u}} [IsEmpty ↥X] {V : X.Opens}
    (hV : IsAffineOpen V) : Subsingleton ↥(X.presheaf.obj (Opposite.op V)) := by
  by_contra hcon
  have : Nontrivial ↥(X.presheaf.obj (Opposite.op V)) :=
    not_subsingleton_iff_nontrivial.mp hcon
  obtain ⟨p⟩ : Nonempty (PrimeSpectrum ↥(X.presheaf.obj (Opposite.op V))) := inferInstance
  exact IsEmpty.false (hV.fromSpec.base p)
private theorem algebra_smooth_of_subsingleton (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Subsingleton S] : Algebra.Smooth R S := by
  have hloc : IsLocalization.Away (0 : R) S :=
    { map_units := fun y => ⟨1, Subsingleton.elim _ _⟩
      surj := fun z => ⟨⟨0, 1⟩, Subsingleton.elim _ _⟩
      exists_of_eq := fun _ => ⟨⟨0, Submonoid.mem_powers 0⟩, by simp⟩ }
  exact ⟨Algebra.FormallySmooth.of_isLocalization (Submonoid.powers (0 : R)),
    IsLocalization.Away.finitePresentation (0 : R)⟩
private theorem ringHom_smooth_of_subsingleton {R S : Type u} [CommRing R] [CommRing S]
    (hS : Subsingleton S) (φ : R →+* S) : RingHom.Smooth φ :=
  @algebra_smooth_of_subsingleton R S _ _ φ.toAlgebra hS
end FunctorialResolution.Blowup
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open FunctorialResolution FunctorialResolution.Blowup
namespace FunctorialResolution.Blowup
theorem _root_.solution {X Y : Scheme.{u}} (f : X ⟶ Y) [IsEmpty ↥X] : Smooth f := by
  constructor
  intro U _ V hV e
  exact ringHom_smooth_of_subsingleton (subsingleton_presheaf_of_isEmpty hV)
    (CommRingCat.Hom.hom (Scheme.Hom.appLE f U V e))
end FunctorialResolution.Blowup
