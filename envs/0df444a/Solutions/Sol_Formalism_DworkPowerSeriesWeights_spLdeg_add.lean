-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.spLdeg_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:12:27.081801+00:00
-- url     : https://prove2.me/submissions/b8658c5c-131b-4c71-bf60-78a099a50eee

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Special

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
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
variable {R : Type*} [CommRing R] {σ : Type*} [Fintype σ] [DecidableEq σ] {ι : Type*} [Fintype ι]
  [DecidableEq ι]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (lt : ι → σ) (t : σ) (n n' : ι →₀ ℕ) :
    spLdeg lt t (n + n') = spLdeg lt t n + spLdeg lt t n' := by
  unfold spLdeg
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp
end Formalism.DworkPowerSeriesWeights
