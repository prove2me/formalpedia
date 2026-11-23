-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BudgetLiftBounds.sizes_tie
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:38.785037+00:00
-- url     : https://prove2.me/submissions/162be050-a472-4694-b2a1-4e87693131c0

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
theorem _root_.solution {E : Type} [Field E] (D : Data E) (Pat3 : Type) [Fintype Pat3] (c1 : E → ℝ)
    (c3 : ℕ → E → ℝ) (ep1 : ℝ) (ep3 bd4 : ℕ → ℝ) (ep a : ℝ) (i : ℕ)
    (h : LevelSizes D Pat3 c1 c3 ep1 ep3 bd4 ep a i) : 0 ≤ ep1 ∧ 1 + ep1 ≤ (1 + ep) ^ 2 := by
  obtain ⟨h1, _, h3, h4, _⟩ := h
  have e1 : 0 ≤ ep1 := by simpa using h1.2 ∅ (by simp)
  refine ⟨e1, le_trans ?_ h4⟩
  have : 0 ≤ (Fintype.card Pat3 : ℝ) * ep3 1 := mul_nonneg (Nat.cast_nonneg _) h3
  nlinarith
end Formalism.FourierDecayAlt.P.BudgetLiftBounds
