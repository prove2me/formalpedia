-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BudgetLiftBounds.bud_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:15.526446+00:00
-- url     : https://prove2.me/submissions/fdbe51c6-02eb-4022-bafc-600b3afc767a

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
theorem _root_.solution (Kl r i n : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ r + 1) (hn : n ≤ 4 * Kl * (r + 1 - i)) :
    n + Kl ≤ 4 * Kl * (r + 1) := by
  generalize r + 1 = M at *
  obtain ⟨d, rfl⟩ : ∃ d, M = i + d := ⟨M - i, by omega⟩
  have e : i + d - i = d := by omega
  rw [e] at hn
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  nlinarith [Nat.zero_le (Kl * j), Nat.zero_le Kl]
end Formalism.FourierDecayAlt.P.BudgetLiftBounds
