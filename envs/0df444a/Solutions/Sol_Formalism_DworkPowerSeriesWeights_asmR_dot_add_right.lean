-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.asmR_dot_add_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:57.25236+00:00
-- url     : https://prove2.me/submissions/874181b2-0756-42be-804a-af838b0da929

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight

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
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {ι : Type v} (n : ι →₀ ℕ) (r s : ι → ℝ) :
    dot n (fun i => r i + s i) = dot n r + dot n s := by
  unfold dot
  simp only [mul_add]
  exact Finsupp.sum_add
end Formalism.DworkPowerSeriesWeights
