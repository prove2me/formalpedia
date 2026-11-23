-- Prove2me | solution 1 for Formalism.FN.partialBoxVolumeTopLeOne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:04.962037+00:00
-- url     : https://prove2.me/submissions/0a4a997b-0387-4606-b78d-230b413872c8

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_MinkCore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Metric Set
open scoped Pointwise ENNReal
noncomputable section
open Formalism Formalism.FN
namespace Formalism.FN
theorem _root_.solution : GjTop := by
  intro n A
  unfold Gj
  calc volume (boxJ n n ∩ (A + latJ n n)) ≤ volume (boxJ n n) :=
        measure_mono Set.inter_subset_left
    _ ≤ volume (Set.univ.pi fun _ : Fin n => Set.Ico (0 : ℝ) 1) := by
        apply measure_mono
        intro u hu i _
        exact hu i i.2
    _ = 1 := by
        rw [Real.volume_pi_Ico]
        simp
end Formalism.FN
