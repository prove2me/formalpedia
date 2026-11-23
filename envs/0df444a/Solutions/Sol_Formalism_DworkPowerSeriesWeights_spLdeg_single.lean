-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.spLdeg_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:05:20.022389+00:00
-- url     : https://prove2.me/submissions/3cfb4f23-acd6-409f-b0a5-a1130a6e7462

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
theorem _root_.solution (lt : ι → σ) (t : σ) (k : ι) (c : ℕ) :
    spLdeg lt t (Finsupp.single k c) = if lt k = t then c else 0 := by
  unfold spLdeg
  rw [Finset.sum_eq_single k]
  · simp
  · intro k' _ hk'
    simp [Ne.symm hk']
  · simp
end Formalism.DworkPowerSeriesWeights
