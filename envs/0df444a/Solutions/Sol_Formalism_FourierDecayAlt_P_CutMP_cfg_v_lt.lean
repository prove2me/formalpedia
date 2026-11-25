-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.cfg_v_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:08:50.218144+00:00
-- url     : https://prove2.me/submissions/f80a6cb2-fe9e-4334-a3ab-5f6edaaef5ee

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
theorem _root_.solution (hok : c.Ok) {i j : ℕ} (hij : i < j) : c.v j < c.v i := by
  have hD := hok.hDel
  have hij' : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij
  simp only [Sz.Cfg.v]
  push_cast
  nlinarith
end Formalism.FourierDecayAlt.P.CutMP
