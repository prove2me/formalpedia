-- Prove2me | solution 1 for Formalism.GM.TM.lg_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:15:53.094427+00:00
-- url     : https://prove2.me/submissions/8f4d735a-d289-4213-8b60-fa22e6d4b7cc

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
namespace Formalism.GM.TM
theorem _root_.solution (p a r : ℕ) [Fact p.Prime] (hr : 2 ≤ r) : 0 ≤ lgV2 p a r := by
  unfold lgV2
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have : (1 : ℝ) ≤ 8 * a + r := by
    have : (2 : ℝ) ≤ r := by exact_mod_cast hr
    have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    linarith
  have := Real.logb_nonneg hp this
  linarith
end Formalism.GM.TM
