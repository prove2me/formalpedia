-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.mem_stripsUp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:45:32.657528+00:00
-- url     : https://prove2.me/submissions/e5abf897-7f42-42da-a023-9ac96424eb06

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
theorem _root_.solution {n : ℕ} (μ ν : Fin n → ℤ) (b : ℕ) : ν ∈ stripsUp μ b ↔ HStrip ν μ b := by
  classical
  unfold stripsUp
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  unfold HStrip
  simp only [Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨fun i => ⟨h.1 i, by linarith [sub_le_sum_sub ν μ h.1 i, h.2.2]⟩, h⟩
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
