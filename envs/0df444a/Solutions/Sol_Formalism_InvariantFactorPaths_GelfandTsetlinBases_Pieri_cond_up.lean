-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.cond_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:54:51.545813+00:00
-- url     : https://prove2.me/submissions/f603ad44-7595-4cce-9c5d-618ae2bbcd43

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_mem_gtBox
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_Lo_le_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_strip2_iff

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
theorem _root_.solution {n : ℕ} (μ ν : Fin (n + 1) → ℤ) (l : Fin n → ℤ) (b : ℕ) :
    (HStrip ν μ b ∧ l ∈ gtBox ν) ↔
      (∀ j, Lo μ l j ≤ ν j) ∧ (∀ i, ν i.succ ≤ Hi μ l i) ∧ ∑ j, ν j - ∑ j, μ j = (b : ℤ) := by
  unfold HStrip
  rw [mem_gtBox, Lo_le_iff, strip2_iff]
  simp only [Hi, le_min_iff]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    exact ⟨⟨h1, fun i => (h4 i).2⟩, fun i => ⟨h2 i, (h4 i).1⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨h1, fun i => (h3 i).1, h4⟩, fun i => ⟨(h3 i).2, h2 i⟩⟩
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
