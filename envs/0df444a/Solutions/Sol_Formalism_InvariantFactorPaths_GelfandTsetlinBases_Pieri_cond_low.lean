-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.cond_low
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:47:59.691848+00:00
-- url     : https://prove2.me/submissions/b233a9da-ec00-49c6-ab4b-6a622dde9d42

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_mem_gtBox
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_mem_sLe
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_Lo_succ_le_iff

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
theorem _root_.solution {n : ℕ} (μ : Fin (n + 1) → ℤ) (κ l : Fin n → ℤ) (b : ℕ) :
    (κ ∈ gtBox μ ∧ l ∈ sLe κ b) ↔
      (∀ i, Lo μ l i.succ ≤ κ i) ∧ (∀ i, κ i ≤ Hi μ l i) ∧ ∑ i, l i - ∑ i, κ i ≤ (b : ℤ) := by
  rw [mem_gtBox, mem_sLe, Lo_succ_le_iff]
  simp only [Hi, le_min_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨fun i => (h1 i).1, h3⟩, fun i => ⟨(h1 i).2, h2 i⟩, h4⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨fun i => ⟨h1 i, (h3 i).1⟩, fun i => (h3 i).2, h2, h4⟩
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
