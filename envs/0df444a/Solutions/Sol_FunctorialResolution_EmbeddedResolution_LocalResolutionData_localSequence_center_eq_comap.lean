-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.LocalResolutionData.localSequence_center_eq_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:47:40.866051+00:00
-- url     : https://prove2.me/submissions/35ad852c-565c-44db-bae7-86b92bcec98f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_StrongResolution
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_LocalResolutionData

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
attribute [instance] LocalResolutionData.finiteType
open FunctorialResolution.EmbeddedResolution.LocalResolutionData
variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}
namespace FunctorialResolution.EmbeddedResolution.LocalResolutionData
theorem _root_.solution (d : LocalResolutionData k f s) (i : d.cover.I₀) (j : ℕ)
    (hj : j < (d.seq i).length) :
    (d.seq i).center j =
      (s.center (d.reindex i j)).comap
        ((d.schemeAtIsoPullback i j hj.le).hom ≫
          pullback.snd (d.cover.f i) (s.projectionToBase (d.reindex i j))) :=
  (d.comparison i).center_eq j hj
end FunctorialResolution.EmbeddedResolution.LocalResolutionData
