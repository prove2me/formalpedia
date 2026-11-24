-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.hasSum_inv_succ_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:36:50.30667+00:00
-- url     : https://prove2.me/submissions/f29cf11f-f7f6-4420-86fd-63735eae4881

import Definitions.Def_Formalism_LogVandermondeBounds_VandPlace
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LogRatioLowerBoundOfLogVandermondeGap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset
namespace Formalism.LogVandermondeBounds.StandardLattice
theorem _root_.solution : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simpa using h
end Formalism.LogVandermondeBounds.StandardLattice
