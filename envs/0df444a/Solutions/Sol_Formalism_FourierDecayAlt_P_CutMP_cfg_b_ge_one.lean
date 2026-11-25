-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.cfg_b_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:30:11.227653+00:00
-- url     : https://prove2.me/submissions/d6c5035c-2c21-432c-b1f6-6bf81320688d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutMP2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutLam
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_cfg_b_lt

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
theorem _root_.solution (hok : c.Ok) {j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ c.m) : 1 ≤ c.b j := by
  rcases Nat.lt_or_ge 1 j with h | h
  · have := cfg_b_lt c hok (le_refl 1) h hjm
    linarith [hok.hb1]
  · have e : j = 1 := by omega
    subst e
    exact hok.hb1
end Formalism.FourierDecayAlt.P.CutMP
