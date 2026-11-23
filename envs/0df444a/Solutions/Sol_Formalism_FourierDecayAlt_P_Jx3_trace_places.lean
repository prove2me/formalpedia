-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx3.trace_places
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:24.206015+00:00
-- url     : https://prove2.me/submissions/e7740b1c-13b6-45db-ae58-7467b4793719

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Lemmata_FiberEquations_FiberEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualCovolumeChangeOfVariables
import Theorems.Thm_Bl_FiberEquations_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J Module
open scoped ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx3
open InfinitePlace
namespace Formalism.FourierDecayAlt.P.Jx3
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (x : E) :
    ((Algebra.trace ℚ E x : ℚ) : ℝ) = ∑ w : InfinitePlace E, 2 * (w.embedding x).re := by
  first | exact Bl.FiberEquations.goal1 .. | (apply Bl.FiberEquations.goal1 <;> assumption) | (intros; apply Bl.FiberEquations.goal1 <;> assumption)
end Formalism.FourierDecayAlt.P.Jx3
