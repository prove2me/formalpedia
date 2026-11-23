-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G5.two_card_UT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:20.397118+00:00
-- url     : https://prove2.me/submissions/cedce6f9-2aa6-4639-a980-5fa2db1c3404

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G5_card_UT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G5
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.G5
theorem _root_.solution (n : ℕ) : 2 * Fintype.card (UT n) = n * (n - 1) := by
  rw [card_UT, mul_comm]; exact Finset.sum_range_id_mul_two n
end Formalism.FourierDecayAlt.P.G5
