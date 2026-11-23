-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BudgetLiftBounds.le_sq_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:38.882425+00:00
-- url     : https://prove2.me/submissions/9765f4be-6c17-436c-af76-28e9c2969c61

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BudgetLiftSquareRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped ComplexConjugate InnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BudgetLiftBounds
namespace Formalism.FourierDecayAlt.P.BudgetLiftBounds
theorem _root_.solution (x : ℝ) : x ≤ (√x) ^ 2 := by
  rcases le_or_gt 0 x with h | h
  · rw [Real.sq_sqrt h]
  · exact le_trans h.le (sq_nonneg _)
end Formalism.FourierDecayAlt.P.BudgetLiftBounds
