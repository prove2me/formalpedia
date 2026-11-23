-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bnx_single_add_single_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:10.809636+00:00
-- url     : https://prove2.me/submissions/64adfc64-3da9-40ed-ad82-51aca4aaec5e

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm

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
open MvPowerSeries Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {σ : Type*} {x y : σ} (hxy : x ≠ y) (r s i j : ℕ) :
    Finsupp.single x r + Finsupp.single y s = Finsupp.single x i + Finsupp.single y j ↔
      r = i ∧ s = j := by
  constructor
  · intro h
    have h1 := DFunLike.congr_fun h x
    have h2 := DFunLike.congr_fun h y
    simp [Finsupp.single_apply, hxy, hxy.symm] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩
    rfl
end Formalism.DworkPowerSeriesWeights
