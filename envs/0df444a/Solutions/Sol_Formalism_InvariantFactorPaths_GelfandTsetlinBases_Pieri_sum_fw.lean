-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.sum_fw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:49.742961+00:00
-- url     : https://prove2.me/submissions/0396cc21-aa0b-44cb-a1dc-1512305f0bc4

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_sum_Lo_Hi

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
theorem _root_.solution {n : ℕ} (μ ν : Fin (n + 1) → ℤ) (l : Fin n → ℤ) :
    ∑ i, fw μ l ν i = ∑ j, μ j + ∑ i, l i - Lo μ l 0 - ∑ j, ν j + ν 0 := by
  have h1 := sum_Lo_Hi μ l
  have h2 := Fin.sum_univ_succ (Lo μ l)
  have h3 := Fin.sum_univ_succ ν
  simp only [fw, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  linarith
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
