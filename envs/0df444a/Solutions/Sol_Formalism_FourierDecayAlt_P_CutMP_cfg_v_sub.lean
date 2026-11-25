-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.cfg_v_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:00:04.799537+00:00
-- url     : https://prove2.me/submissions/8cc784fc-54a2-4257-8237-6fb9798e50db

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutMP2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutLam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP
variable (c : Sz.Cfg)
namespace Formalism.FourierDecayAlt.P.CutMP
theorem _root_.solution (i : ℕ) : c.v i - c.v (i + 1) = 4 * c.Del := by
  simp only [Sz.Cfg.v]
  push_cast
  ring
end Formalism.FourierDecayAlt.P.CutMP
