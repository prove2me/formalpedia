-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths.colHeight_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:38:53.1469+00:00
-- url     : https://prove2.me/submissions/7e45280c-bda3-492c-a682-631bb44d4e22

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight

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
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Paths
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths
theorem _root_.solution (n : ℕ) (c : ℤ) : colHeight (0 : Fin n → ℤ) c = if 1 ≤ c then 0 else n := by
  unfold colHeight
  by_cases hc : 1 ≤ c
  · rw [if_pos hc, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro m _
    simp only [Pi.zero_apply]
    omega
  · rw [if_neg hc, Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]
    intro m _
    simp only [Pi.zero_apply]
    omega
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Paths
