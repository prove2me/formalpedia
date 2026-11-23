-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.spLdeg_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:46.622904+00:00
-- url     : https://prove2.me/submissions/87a577ee-ff5c-4872-b178-79fe8f831bfb

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
theorem _root_.solution (lt : ι → σ) (n : ι →₀ ℕ) (k : ι) (h : spLdeg lt (lt k) n = 0) :
    n k = 0 := by
  unfold spLdeg at h
  have := (Finset.sum_eq_zero_iff.mp h) k (Finset.mem_univ _)
  simpa using this
end Formalism.DworkPowerSeriesWeights
