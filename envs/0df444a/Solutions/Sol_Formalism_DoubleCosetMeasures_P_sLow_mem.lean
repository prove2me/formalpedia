-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.sLow_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:28.823066+00:00
-- url     : https://prove2.me/submissions/ad97e5de-f32d-4227-a08c-88eb1a8e1b0f

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (x : Matrix (Fin n) (Fin n) K)
    (hx : IsInt R x) : sLow x ∈ R := by
  unfold sLow
  refine R.sum_mem fun j _ => ?_
  split_ifs
  · exact hx _ _
  · exact R.zero_mem
end Formalism.DoubleCosetMeasures.P
