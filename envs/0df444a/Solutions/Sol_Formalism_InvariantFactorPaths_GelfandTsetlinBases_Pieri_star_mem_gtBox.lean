-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.star_mem_gtBox
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:49.523159+00:00
-- url     : https://prove2.me/submissions/55fb7ae6-1715-46c1-a42a-0de43269903a

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_mem_gtBox

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
theorem _root_.solution {n : ℕ} {μ : Fin (n + 1) → ℤ} {κ : Fin n → ℤ} (h : κ ∈ gtBox μ) :
    star κ ∈ gtBox (star μ) := by
  rw [mem_gtBox] at h ⊢
  intro i
  simp only [star]
  have h1 := h i.rev
  rw [Fin.rev_succ, Fin.rev_castSucc]
  exact ⟨neg_le_neg h1.2, neg_le_neg h1.1⟩
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
