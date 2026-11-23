-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.mem_stripsDown
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:49.429117+00:00
-- url     : https://prove2.me/submissions/68c24c87-8448-47e4-9243-57182305f192

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_sub_le_sum_sub

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
theorem _root_.solution {n : ℕ} (μ ν : Fin n → ℤ) (b : ℕ) : ν ∈ stripsDown μ b ↔ HStrip μ ν b := by
  classical
  unfold stripsDown
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  unfold HStrip
  simp only [Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨fun i => ⟨by linarith [sub_le_sum_sub μ ν h.1 i, h.2.2, h.1 i],
      by linarith [sub_le_sum_sub μ ν h.1 i, h.2.2, h.1 i]⟩, h⟩
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
