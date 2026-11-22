-- Prove2me | solution 1 for Formalism.REAL.continuous_hs_real_place_taylor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:42:38.26363+00:00
-- url     : https://prove2.me/submissions/ceeeeacf-c574-4d4d-a67c-2d39e772c43e

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} : Continuous (hs : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  unfold hs
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    ((continuous_apply j).comp (continuous_apply i)).norm.pow 2
end Formalism.REAL
