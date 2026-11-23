-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.dot_const_wt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:58:29.760903+00:00
-- url     : https://prove2.me/submissions/4599f786-c921-4084-b3ff-9017314e9f1d

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneLetterRadiusIdentity

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
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {ι : Type*} (n : ι →₀ ℕ) (c : ℝ) :
    dot n (fun _ => c) = (∑ x ∈ n.support, (n x : ℝ)) * c := by
  simp only [dot, Finsupp.sum, Finset.sum_mul]
end Formalism.DworkPowerSeriesWeights
