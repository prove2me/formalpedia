-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.coord_units_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:06:53.039748+00:00
-- url     : https://prove2.me/submissions/acf31dcb-1dac-4965-9d9c-3fd76c73e6cd

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_coord_smul_self
import Theorems.Thm_Formalism_MainNotions_Gaps_EtaleWeightGaps_isGen_units_smul

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
variable {V : Type*} [AddCommGroup V] [Module A V] {ϖ : O} {e : V} (c : Pts O A → ℤ)
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps
theorem _root_.solution (he : IsGen A e) (u : Aˣ) (v : V) :
    (coord ((u : A) • e) v : A) * u = coord e v := by
  apply he.1
  change ((coord ((u : A) • e) v : A) * u) • e = (coord e v : A) • e
  rw [mul_smul, coord_smul_self (isGen_units_smul he u), coord_smul_self he]
end Formalism.MainNotions.Gaps.EtaleWeightGaps
