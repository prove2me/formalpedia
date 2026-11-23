-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BudgetLiftBounds.bud_block
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:15.593888+00:00
-- url     : https://prove2.me/submissions/893ef18d-10ca-4e9f-b37f-d526cfa0912a

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
theorem _root_.solution (Kl r i s n n' : ℕ) (hs : 2 ≤ s) (hsi : s ≤ i) (h2 : i ≤ r + 1)
    (hn : n ≤ 4 * Kl * (r + 1 - i)) (hn' : n' ≤ n + Kl) :
    n' + (s + 1) * Kl ≤ 4 * Kl * (r + 1 - (i - s)) ∧
      4 * Kl * (r + 1 - (i - s)) ≤ 4 * Kl * (r + 1) := by
  generalize r + 1 = M at *
  obtain ⟨d, rfl⟩ : ∃ d, M = i + d := ⟨M - i, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = j + s := ⟨i - s, by omega⟩
  have e : j + s + d - (j + s) = d := by omega
  have e' : j + s + d - (j + s - s) = d + s := by omega
  rw [e] at hn
  rw [e']
  obtain ⟨u, rfl⟩ : ∃ u, s = u + 2 := ⟨s - 2, by omega⟩
  constructor
  · nlinarith [Nat.zero_le (Kl * u), Nat.zero_le Kl]
  · nlinarith [Nat.zero_le (Kl * j)]
end Formalism.FourierDecayAlt.P.BudgetLiftBounds
