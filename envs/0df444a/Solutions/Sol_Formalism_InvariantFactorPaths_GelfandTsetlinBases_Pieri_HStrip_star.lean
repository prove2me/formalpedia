-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.HStrip_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:47:57.47585+00:00
-- url     : https://prove2.me/submissions/609429d9-3e82-40ec-ae97-f4768fe29750

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_sum_star

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
theorem _root_.solution {n : ℕ} {μ ν : Fin n → ℤ} {b : ℕ} (h : HStrip μ ν b) : HStrip (star ν) (star μ) b := by
  unfold HStrip at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun m => ?_, fun m m' hm => ?_, ?_⟩
  · simp only [star]
    exact neg_le_neg (h1 _)
  · simp only [star]
    apply neg_le_neg
    apply h2
    have := m'.isLt
    simp only [Fin.val_rev]
    omega
  · rw [sum_star, sum_star]
    linarith
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
