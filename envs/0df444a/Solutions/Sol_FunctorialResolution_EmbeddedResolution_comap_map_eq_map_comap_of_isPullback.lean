-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.comap_map_eq_map_comap_of_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:18:43.084804+00:00
-- url     : https://prove2.me/submissions/d6b05015-0f81-4e7f-9c51-6e0d81cebf62

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_IdealSheafFlatComapInjective
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_KernelFlatBaseChange
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_IdealSheafFlatDescent
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_ker_eq_comap_ker_of_isPullback_of_flat
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_quasiCompact_of_isPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
open CategoryTheory Limits AlgebraicGeometry
namespace FunctorialResolution.EmbeddedResolution
private theorem map_eq_ker {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : X ⟶ Y) :
    I.map f = (I.subschemeι ≫ f).ker := rfl
private theorem comap_eq_ker_pullback_fst {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) :
    I.comap f = (pullback.fst f I.subschemeι).ker := rfl
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
universe u
open CategoryTheory Limits AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {W X X' W' : Scheme.{u}} {f : W ⟶ X} {g : X' ⟶ X}
    {g' : W' ⟶ W} {f' : W' ⟶ X'} (H : IsPullback g' f' f g)
    [QuasiCompact f] [AlgebraicGeometry.Flat g] (I : W.IdealSheafData) :
    (I.map f).comap g = (I.comap g').map f' := by
  have hqc : QuasiCompact (I.subschemeι ≫ f) := inferInstance
  have S : IsPullback (pullback.snd g' I.subschemeι) (pullback.fst g' I.subschemeι ≫ f')
      (I.subschemeι ≫ f) g := (IsPullback.of_hasPullback g' I.subschemeι).flip.paste_vert H
  have hqc' : QuasiCompact (pullback.fst g' I.subschemeι ≫ f') := quasiCompact_of_isPullback S
  have h1 := ker_eq_comap_ker_of_isPullback_of_flat S
  rw [map_eq_ker, ← h1, Scheme.Hom.ker_comp, comap_eq_ker_pullback_fst]
end FunctorialResolution.EmbeddedResolution
