-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.asmR_dot_pureMon
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:42:12.935853+00:00
-- url     : https://prove2.me/submissions/05d37e72-c2b4-4216-908f-c77d8013ec7d

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
theorem _root_.solution {ι : Type v} [DecidableEq ι] (l : ℕ) (i j : ι) (α β : ℕ) (r : ι → ℝ) :
    dot (pureMon l i j α β) r = (l : ℝ) ^ α * r i + (l : ℝ) ^ β * r j := by
  unfold pureMon dot
  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; ring),
    Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
  push_cast
  ring
end Formalism.DworkPowerSeriesWeights
