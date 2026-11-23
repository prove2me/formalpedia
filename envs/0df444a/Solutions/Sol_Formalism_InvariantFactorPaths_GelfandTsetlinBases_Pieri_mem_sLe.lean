-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.mem_sLe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:49.621328+00:00
-- url     : https://prove2.me/submissions/c56deee9-2032-4958-9f7d-425dd75f46e6

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
theorem _root_.solution {n : ℕ} (κ l : Fin n → ℤ) (b : ℕ) :
    l ∈ sLe κ b ↔ (∀ m, κ m ≤ l m) ∧ (∀ m m' : Fin n, m.val + 1 = m'.val → l m' ≤ κ m) ∧
      ∑ m, l m - ∑ m, κ m ≤ (b : ℤ) := by
  unfold sLe
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun i => Finset.mem_Icc.mpr ⟨h.1 i, ?_⟩, h⟩
    have := sub_le_sum_sub l κ h.1 i
    linarith [h.2.2]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
