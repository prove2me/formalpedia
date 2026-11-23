-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz1.disc_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:21.121398+00:00
-- url     : https://prove2.me/submissions/6727d40c-921f-426c-ba3f-bfc7bad86261

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MassRatioFormula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz1
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz1
theorem _root_.solution (rd : ℝ) (hrd : 0 < rd) (f p : ℕ) :
    ((rd ^ f) ^ (-(1 / 2 : ℝ))) ^ p = (rd ^ (-((p : ℝ) / 2))) ^ f := by
  rw [← Real.rpow_natCast rd f, ← Real.rpow_mul hrd.le, ← Real.rpow_natCast _ p,
    ← Real.rpow_mul hrd.le, ← Real.rpow_natCast _ f, ← Real.rpow_mul hrd.le]
  congr 1; ring
end Formalism.FourierDecayAlt.P.Sz1
