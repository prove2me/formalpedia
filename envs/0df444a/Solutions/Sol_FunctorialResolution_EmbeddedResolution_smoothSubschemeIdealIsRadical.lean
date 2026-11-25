-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.smoothSubschemeIdealIsRadical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:24:28.045595+00:00
-- url     : https://prove2.me/submissions/94678ee9-4435-4cec-9daa-832e09f842b1

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_SmoothRegular
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_PrincipalizationConstruction
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_RadicalCenterIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isDomain_stalk_of_smooth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
private theorem radical_ker_le_ker_of_isReduced {R S : Type*} [CommRing R] [CommRing S] [IsReduced S]
    (f : R →+* S) : (RingHom.ker f).radical ≤ RingHom.ker f := by
  intro x hx
  obtain ⟨n, hn⟩ := hx
  rw [RingHom.mem_ker, map_pow] at hn
  rw [RingHom.mem_ker]
  exact IsNilpotent.eq_zero ⟨n, hn⟩
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution : SmoothSubschemeIdealIsRadical.{u} := by
  intro k ik X p Z ism J hsub
  have hstalk : ∀ x : ↥Z.subscheme, _root_.IsReduced ↑(Z.subscheme.presheaf.stalk x) := by
    intro x
    have := isDomain_stalk_of_smooth (Z.subschemeι ≫ p) x
    infer_instance
  have hred : AlgebraicGeometry.IsReduced Z.subscheme :=
    isReduced_of_isReduced_stalk Z.subscheme
  have hcomp : ∀ U : Z.subscheme.Opens,
      _root_.IsReduced ↑(Z.subscheme.presheaf.obj (Opposite.op U)) :=
    fun U => AlgebraicGeometry.IsReduced.component_reduced U
  have hZrad : ∀ U : X.affineOpens, (Z.ideal U).radical ≤ Z.ideal U := by
    intro U
    rw [← Z.ker_subschemeι_app U]
    exact radical_ker_le_ker_of_isReduced _
  have hle : Z.support ≤ J.support := SetLike.coe_subset_coe.mp hsub
  have hJv : J ≤ Scheme.IdealSheafData.vanishingIdeal Z.support := by
    apply (Scheme.IdealSheafData.gc J Z.support).mp
    exact hle
  rw [Scheme.IdealSheafData.vanishingIdeal_support] at hJv
  have hrad : Z.radical ≤ Z := by
    rw [Scheme.IdealSheafData.le_def]
    intro U
    rw [Scheme.IdealSheafData.radical_ideal]
    exact hZrad U
  exact le_trans hJv hrad
end FunctorialResolution.EmbeddedResolution
