-- Prove2me | solution 1 for Formalism.DivisionValues.W8.log_nat_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:05:58.798817+00:00
-- url     : https://prove2.me/submissions/4b77bc61-7a64-4369-81c1-2b3a4b220e0a

import Definitions.Def_Formalism_QuotientMetricDivisors_TheoremDivIneqRows
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SumInterlacedBoundFails
import Definitions.Def_Formalism_LogFactorialIndices_SubspaceIndexSigned
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_YoungDiagramHook

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.LatticeIndexTer (ph)
open Formalism.DivisionValues.W8
namespace Formalism.DivisionValues.W8
theorem _root_.solution {A : ℝ} (r : ℕ) (hA : 1 ≤ Real.log A) (hr : (r : ℝ) ≤ A) :
    Real.log (r : ℝ) ≤ Real.log A := by
  rcases Nat.eq_zero_or_pos r with h0 | h0
  · subst h0
    simp only [Nat.cast_zero, Real.log_zero]
    linarith
  · exact Real.log_le_log (by exact_mod_cast h0) hr
end Formalism.DivisionValues.W8
