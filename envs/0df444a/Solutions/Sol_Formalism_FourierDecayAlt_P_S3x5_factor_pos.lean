-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.factor_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:58:55.208911+00:00
-- url     : https://prove2.me/submissions/639c3e2a-69ca-432f-9ba0-4959cec5d371

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_qpow_le_half
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_factor_bounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Finset Formalism.FourierDecayAlt.S3
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution (η : ℤ) (hη : η = 1 ∨ η = -1) (q : ℕ) (hq : 2 ≤ q) (i : ℤ) (hi : 1 ≤ i) :
    0 < 1 - (η : ℝ) ^ i * (q : ℝ) ^ (-i) := by
  have := (factor_bounds η hη q hq i hi).1
  have := qpow_le_half q hq i hi
  linarith
end Formalism.FourierDecayAlt.P.S3x5
