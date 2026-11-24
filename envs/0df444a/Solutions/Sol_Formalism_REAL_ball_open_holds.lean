-- Prove2me | solution 1 for Formalism.REAL.ball_open_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:34:18.098079+00:00
-- url     : https://prove2.me/submissions/2dea3929-055d-4e3c-a7f9-a78d718b5d3a

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Theorems.Thm_Formalism_REAL_continuous_hs_real_place_taylor
import Theorems.Thm_Formalism_REAL_f1auxiliary_hs_one

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
theorem _root_.solution : BallOpen := by
  intro n R hR
  refine ⟨{g | hs g < R}, isOpen_lt continuous_hs_real_place_taylor continuous_const, ?_, fun g hg => hg⟩
  show hs (1 : Matrix (Fin n) (Fin n) ℂ) < R
  rw [f1auxiliary_hs_one]
  exact hR
end Formalism.REAL
