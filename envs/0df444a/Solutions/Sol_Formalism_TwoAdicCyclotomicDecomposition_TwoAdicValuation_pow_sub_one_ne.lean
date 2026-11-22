-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation.pow_sub_one_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:16:02.916461+00:00
-- url     : https://prove2.me/submissions/9ca869b5-b8a7-4cc1-8119-18b7722ebc6b

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_TwoAdic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.TwoAdicCyclotomicDecomposition Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation
namespace Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation
theorem _root_.solution (a : ℤ) (ha2 : a ^ 2 ≠ 1) (e : ℕ) (he : 0 < e) : a ^ e - 1 ≠ 0 := by
  intro h
  apply ha2
  have h1 : |a| ^ e = 1 := by rw [pow_abs, sub_eq_zero.mp h, abs_one]
  have h2 : |a| = 1 := (pow_eq_one_iff_of_nonneg (abs_nonneg a) he.ne').mp h1
  rw [← sq_abs, h2, one_pow]
end Formalism.TwoAdicCyclotomicDecomposition.TwoAdicValuation
