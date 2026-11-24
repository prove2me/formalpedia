-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.StandardLattice.log_zetaR_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:53:02.559544+00:00
-- url     : https://prove2.me/submissions/ca2b0709-179c-4f7a-96c5-295c34a6785d

import Definitions.Def_Formalism_LogVandermondeBounds_UpperPlace
import Mathlib
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LogRatioUpperBoundOfUpperPlace
import Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_zetaR_le_two

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
theorem _root_.solution {M : ℕ} (hM : 2 ≤ M) : Real.log (zetaR M) ≤ 2 := by
  have h0 : 0 ≤ zetaR M := tsum_nonneg (fun n => by positivity)
  exact (Real.log_le_self h0).trans (zetaR_le_two hM)
end Formalism.LogVandermondeBounds.StandardLattice
