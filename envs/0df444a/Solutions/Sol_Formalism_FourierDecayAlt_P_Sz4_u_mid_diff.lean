-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz4.u_mid_diff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:55.337792+00:00
-- url     : https://prove2.me/submissions/75a0dbed-022c-4fa0-bee1-43f54e87ef88

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_u_mid

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz4
open Finset Formalism.FourierDecayAlt.Sz
namespace Formalism.FourierDecayAlt.P.Sz4
theorem _root_.solution (c : Cfg) (de de' : ℕ → ℝ) (hc : c.Ok) (hw : IsWord c.k de)
    (hw' : IsWord c.k de') (i : ℕ) (hi : i ∈ Icc 2 (c.k - 1)) :
    |c.u de i - c.u de' i| ≤ c.Del := by
  rw [u_mid c de hw i hi, u_mid c de' hw' i hi]
  have hD := hc.hDel
  rw [abs_le]
  rcases hw.1 (i - 1) with e | e <;> rcases hw'.1 (i - 1) with e' | e' <;> rw [e, e'] <;>
    constructor <;> linarith
end Formalism.FourierDecayAlt.P.Sz4
