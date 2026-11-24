-- Prove2me | solution 1 for Formalism.LogFactorialMertensBounds.hasDerivAt_P
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:36:48.919988+00:00
-- url     : https://prove2.me/submissions/d31a7938-90d0-4ae8-b22b-579aa5e888cd

import Definitions.Def_Formalism_StatementU
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ArithmeticFunction
noncomputable section
open Formalism
open Formalism.LogFactorialMertensBounds
namespace Formalism.LogFactorialMertensBounds
theorem _root_.solution (k : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (P k) (A k - Real.log x + Real.eulerMascheroniConstant) x := by
  have h1 := ((((hasDerivAt_id' (x := x)).mul_const (A k)).sub_const
    (∑ n ∈ Finset.Ioc 0 k, Λ n)).sub (Real.hasDerivAt_mul_log hx.ne')).add
    ((hasDerivAt_id' (x := x)).const_mul (1 + Real.eulerMascheroniConstant))
  refine (h1.congr_deriv (by ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  simp only [P, Pi.add_apply, Pi.sub_apply]
end Formalism.LogFactorialMertensBounds
