-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BudgetLiftBounds.wsup_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:38.805768+00:00
-- url     : https://prove2.me/submissions/a4f94155-728f-4971-83f8-faa2cde45015

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
theorem _root_.solution {W : Type} (len : W → ℕ) (B : ℕ) (g : W → ℝ) (M : ℝ) (w0 : W) (h0 : len w0 ≤ B)
    (h : ∀ w, len w ≤ B → g w ≤ M) : wsup len B g ≤ M := by
  have : Nonempty {w // len w ≤ B} := ⟨⟨w0, h0⟩⟩
  exact ciSup_le fun w => h w.1 w.2
end Formalism.FourierDecayAlt.P.BudgetLiftBounds
