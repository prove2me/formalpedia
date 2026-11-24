-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.Lo_succ_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:49.387311+00:00
-- url     : https://prove2.me/submissions/5cca5462-97ea-4258-922a-62083b5f518d

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
theorem _root_.solution {n : ℕ} (μ : Fin (n + 1) → ℤ) (κ l : Fin n → ℤ) :
    (∀ i : Fin n, Lo μ l i.succ ≤ κ i) ↔
      (∀ i : Fin n, μ i.succ ≤ κ i) ∧ (∀ m m' : Fin n, m.val + 1 = m'.val → l m' ≤ κ m) := by
  constructor
  · intro h
    refine ⟨fun i => le_trans (le_max_left _ _) (h i), fun m m' hm => ?_⟩
    have e : m.succ = m'.castSucc := Fin.ext (by simp only [Fin.val_succ, Fin.coe_castSucc]; exact hm)
    have := h m
    unfold Lo at this
    rw [e, Fin.snoc_castSucc] at this
    exact le_trans (le_max_right _ _) this
  · rintro ⟨h1, h2⟩ i
    unfold Lo
    refine max_le (h1 i) ?_
    have hi0 := i.isLt
    by_cases hi : i.val + 1 < n
    · have e : i.succ = (⟨i.val + 1, hi⟩ : Fin n).castSucc :=
        Fin.ext (by simp only [Fin.val_succ, Fin.coe_castSucc])
      rw [e, Fin.snoc_castSucc]
      exact h2 i _ rfl
    · have e : i.succ = Fin.last n := Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
      rw [e, Fin.snoc_last, ← e]
      exact h1 i
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
