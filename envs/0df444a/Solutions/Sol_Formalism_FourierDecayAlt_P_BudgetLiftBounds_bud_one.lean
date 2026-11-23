-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BudgetLiftBounds.bud_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:15.530467+00:00
-- url     : https://prove2.me/submissions/681fb9ad-97eb-4bff-9b22-44f9efda703f

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
theorem _root_.solution (Kl r i n n' : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ r + 1) (hn : n ≤ 4 * Kl * (r + 1 - i))
    (hn' : n' ≤ n + Kl) :
    n' + Kl ≤ 4 * Kl * (r + 1 - (i - 1)) ∧ 4 * Kl * (r + 1 - (i - 1)) ≤ 4 * Kl * (r + 1) := by
  generalize r + 1 = M at *
  obtain ⟨d, rfl⟩ : ∃ d, M = i + d := ⟨M - i, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have e : j + 1 + d - (j + 1) = d := by omega
  have e' : j + 1 + d - (j + 1 - 1) = d + 1 := by omega
  rw [e] at hn
  rw [e']
  constructor
  · nlinarith [Nat.zero_le Kl]
  · nlinarith [Nat.zero_le (Kl * j)]
end Formalism.FourierDecayAlt.P.BudgetLiftBounds
