-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G6.isStrictUpper_strictUpper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:55:59.530829+00:00
-- url     : https://prove2.me/submissions/cac44017-1134-4668-b232-ed5ba5a11209

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G6
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.G6
theorem _root_.solution {d : ℕ} (v : UT d → ℂ) : IsStrictUpper (strictUpper v) := by
  intro i j h
  simp [strictUpper, not_lt.mpr h]
end Formalism.FourierDecayAlt.P.G6
