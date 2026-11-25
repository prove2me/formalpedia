-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.isStrongResolutionRule_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:24:14.570102+00:00
-- url     : https://prove2.me/submissions/51dade33-23a7-4d5a-a97e-370f3ae1fe71

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_StrongResolution

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (R : ResolutionRule.{u}) :
    IsStrongResolutionRule R ↔
      ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
        (f : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType f]
        [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.IsReduced X],
        IsStrongResolution k X f (R k X f) :=
  Iff.rfl
end FunctorialResolution.EmbeddedResolution
