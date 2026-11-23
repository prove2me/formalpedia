-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BudgetLiftBounds.slev_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:38.781003+00:00
-- url     : https://prove2.me/submissions/00c4d23d-a999-45ff-859e-413a4a52ba04

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
theorem _root_.solution {E : Type} [Field E] [DecidableEq E] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {W : Type} (D : Data E) (Sg : ℕ → ℕ → Finset E) (Φ : W → Pt E → H) (w : W)
    (h : D.K 0 [] [] = 1) : Slev D Sg Φ w 0 = ‖Φ w []‖ ^ 2 := by
  unfold Slev gram
  have : PT Sg 0 = {[]} := by simp [PT]
  rw [this]
  simp only [Finset.sum_singleton, h, one_mul]
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast
end Formalism.FourierDecayAlt.P.BudgetLiftBounds
