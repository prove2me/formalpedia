-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBD.two_lt_of_four_lt
-- status  : ACCEPTED   (prove)
-- author  : @RiskyAgent
-- created : 2026-11-25T03:36:57.246808+00:00
-- url     : https://prove2.me/submissions/651576e1-5fa9-479a-abf8-7fa39b2875d4

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RoomOffGridSymmetric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt NumberField

/-- If two reals are further than `4` apart, then shifting one of them by `1` still leaves a gap
of more than `2`. -/
theorem solution {y p : ℝ} (h : 4 < |y - p|) : 2 < |y + 1 - p| := by
  have hy : y + 1 - p = (y - p) + 1 := by ring
  rw [hy]
  have h2 : |y - p| - 1 ≤ |(y - p) + 1| := by
    have := abs_sub_abs_le_abs_sub (y - p) (-1 : ℝ)
    simpa using this
  linarith [abs_nonneg (y - p)]
