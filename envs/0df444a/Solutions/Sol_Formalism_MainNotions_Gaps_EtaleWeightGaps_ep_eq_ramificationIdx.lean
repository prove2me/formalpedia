-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.ep_eq_ramificationIdx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:57.981975+00:00
-- url     : https://prove2.me/submissions/d546aeff-302d-40c8-b03f-8c9f28e87597

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps
variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable (A : Type*) [CommRing A] [Algebra O A]
variable {O A}
attribute [instance] IsDVRAt.isDomain IsDVRAt.isDVR
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps
theorem _root_.solution {ϖ : O} (hϖ : Irreducible ϖ) (ζ : Pts O A) :
    ep ϖ ζ = ζ.asIdeal.ramificationIdx O := by
  have h1 : (ζ.asIdeal.under O).map (algebraMap O (Loc ζ))
      = Ideal.span {algebraMap ↥(As O A) (Loc ζ) (algebraMap O ↥(As O A) ϖ)} := by
    rw [Ideal.under_def, comap_eq_maximalIdeal, hϖ.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton, ← IsScalarTower.algebraMap_apply]
  rw [Ideal.ramificationIdx_def, h1]
  rfl
end Formalism.MainNotions.Gaps.EtaleWeightGaps
