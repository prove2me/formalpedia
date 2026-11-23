-- Prove2me | solution 1 for Formalism.GM.ProgressionMeanBounds.swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:50.980897+00:00
-- url     : https://prove2.me/submissions/57338632-2e0d-460c-85c4-8baa8f18d810

import Definitions.Def_Formalism_MahlerMeasure_QuotientUpperBoundsOfPowerBounds
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_DeterminantBlockLeadingTerm
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WindowMeanAP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Formalism.GM.ProgressionMeanBounds
open Finset Polynomial
namespace Formalism.GM.ProgressionMeanBounds
theorem _root_.solution {K ι : Type} (W : Finset ι) (roots : Multiset K) (f : ι → K → ℝ) :
    ∑ t ∈ W, (roots.map (f t)).sum = (roots.map (fun ζ => ∑ t ∈ W, f t ζ)).sum := by
  induction roots using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [Finset.sum_add_distrib, ih]
end Formalism.GM.ProgressionMeanBounds
