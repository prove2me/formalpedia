-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BudgetLiftBounds.le_wsup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:31:40.884728+00:00
-- url     : https://prove2.me/submissions/86559db8-2fec-4171-812b-284e27b126ae

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
theorem _root_.solution {W : Type} [Finite W] (len : W → ℕ) (B : ℕ) (g : W → ℝ) (w : W) (h : len w ≤ B) :
    g w ≤ wsup len B g :=
  le_ciSup (f := fun w : {w // len w ≤ B} => g w.1) (Set.finite_range _).bddAbove ⟨w, h⟩
end Formalism.FourierDecayAlt.P.BudgetLiftBounds
