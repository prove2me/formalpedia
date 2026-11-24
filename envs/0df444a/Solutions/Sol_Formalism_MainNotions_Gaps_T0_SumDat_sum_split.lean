-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.SumDat.sum_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:40:14.477957+00:00
-- url     : https://prove2.me/submissions/7656841d-28e2-4041-a423-10bdf12a5fa0

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
theorem _root_.solution (X : SumDat ι) :
    ∑ la ∈ X.s, X.rr la * X.l la =
      X.R * (∑ la ∈ X.s, X.I la * X.l la + 1 / 2 * (X.T * (X.c / X.i) * ∑ la ∈ X.s, X.N la * X.l la))
        + ∑ la ∈ X.s, X.cD la * X.l la + ∑ la ∈ X.s, (X.vQ la + X.ρ' * X.be la) * X.l la := by
  have e : ∀ la, X.rr la * X.l la = X.R * (X.I la * X.l la) +
      X.R * (1 / 2 * (X.T * (X.c / X.i))) * (X.N la * X.l la) + X.cD la * X.l la +
        (X.vQ la + X.ρ' * X.be la) * X.l la := fun la => by
    unfold SumDat.rr
    ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring
end Formalism.MainNotions.Gaps.T0.SumDat
