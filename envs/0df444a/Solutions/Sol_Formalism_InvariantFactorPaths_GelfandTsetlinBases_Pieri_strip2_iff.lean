-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.strip2_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:49.549807+00:00
-- url     : https://prove2.me/submissions/9b09b177-f996-4ed7-8343-015c0114f143

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
theorem _root_.solution {n : ℕ} (μ ν : Fin (n + 1) → ℤ) :
    (∀ m m' : Fin (n + 1), m.val + 1 = m'.val → ν m' ≤ μ m) ↔ ∀ i : Fin n, ν i.succ ≤ μ i.castSucc := by
  constructor
  · intro h i
    exact h i.castSucc i.succ (by simp only [Fin.val_succ, Fin.coe_castSucc])
  · intro h m m' hm
    have hlt : m.val < n := by have := m'.isLt; omega
    obtain ⟨i, rfl⟩ : ∃ i : Fin n, m = i.castSucc := ⟨⟨m.val, hlt⟩, Fin.ext rfl⟩
    simp only [Fin.coe_castSucc] at hm
    have e2 : m' = i.succ := Fin.ext (by simp only [Fin.val_succ]; omega)
    subst e2
    exact h i
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
