-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.sum_bw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:06.637569+00:00
-- url     : https://prove2.me/submissions/c99fb936-8391-483a-9652-4fc90114c8f4

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
theorem _root_.solution {n : ℕ} (μ : Fin (n + 1) → ℤ) (κ l : Fin n → ℤ) (b : ℕ) :
    ∑ j, bw μ l b κ j = ∑ j, μ j + b := by
  have h1 := sum_Lo_Hi μ l
  have h2 := Fin.sum_univ_succ (Lo μ l)
  rw [Fin.sum_univ_succ (bw μ l b κ)]
  simp only [bw, Fin.cons_zero, Fin.cons_succ, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  linarith
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
