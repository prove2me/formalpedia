-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.SumDat.rr_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:17:49.51221+00:00
-- url     : https://prove2.me/submissions/1abaf1f6-0a9a-4a0c-a3a3-9004307994fe

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_FourTermSumBoundOfParameters
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_QuotientParamNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.T0
open Formalism.MainNotions.Gaps.T0.SumDat
variable {ι : Type*} (X : SumDat ι)
variable {X}
namespace Formalism.MainNotions.Gaps.T0.SumDat
theorem _root_.solution (X : SumDat ι) (la : ι) (h1 : 0 ≤ X.R * X.I la)
    (h2 : 0 ≤ X.R * (X.T * (X.c / (2 * X.i)) * X.N la)) (h3 : 0 ≤ X.cD la)
    (h4 : 0 ≤ X.vQ la + X.ρ' * X.be la) : 0 ≤ X.rr la := by
  unfold SumDat.rr
  rw [mul_add]
  linarith
end Formalism.MainNotions.Gaps.T0.SumDat
