-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.pairExp_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:43:37.997892+00:00
-- url     : https://prove2.me/submissions/b993b6e6-7fb4-4a5c-b0fd-47bc9d4357a7

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {ι : Type} [Fintype ι] (n : ι → ℕ) (b : Bool) (i : ι) :
    pairExp n (b, i) = n i := by
  classical
  unfold pairExp
  rw [Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single i]
  · cases b <;> simp
  · intro j _ hj
    cases b <;> simp [hj]
  · intro h; exact absurd (Finset.mem_univ i) h
end Formalism.DworkPowerSeriesWeights
