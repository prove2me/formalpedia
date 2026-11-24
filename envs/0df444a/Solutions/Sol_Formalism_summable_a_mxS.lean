-- Prove2me | solution 1 for Formalism.summable_a_mxS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:46:32.176591+00:00
-- url     : https://prove2.me/submissions/1462269e-3ff7-4478-a20a-f2ddc5b2e70b

import Definitions.Def_Formalism_DefsOC
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSAux
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Theorems.Thm_Formalism_a_mxS_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology ArithmeticFunction
noncomputable section
open Formalism
variable (a : ℕ → ℝ)
namespace Formalism
theorem _root_.solution (ha0 : a 0 = 0) (x : ℝ) : Summable (fun n => a n * mxS n x) :=
  summable_of_ne_finset_zero (s := Finset.Icc 1 ⌊x⌋₊) (fun n hn => a_mxS_eq_zero a ha0 x n hn)
end Formalism
