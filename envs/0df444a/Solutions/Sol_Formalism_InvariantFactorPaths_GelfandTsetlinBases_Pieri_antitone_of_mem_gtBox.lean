-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.antitone_of_mem_gtBox
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:49.414341+00:00
-- url     : https://prove2.me/submissions/7afc5c16-898c-431c-8476-43a62e555802

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
theorem _root_.solution {n : ℕ} {μ : Fin (n + 1) → ℤ} {κ : Fin n → ℤ} (hμ : Antitone μ)
    (hκ : κ ∈ gtBox μ) : Antitone κ := by
  rw [mem_gtBox] at hκ
  intro i j hij
  rcases eq_or_lt_of_le hij with h | h
  · rw [h]
  · calc κ j ≤ μ j.castSucc := (hκ j).2
      _ ≤ μ i.succ := hμ (Fin.succ_le_castSucc_iff.mpr h)
      _ ≤ κ i := (hκ i).1
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
