-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.sum_Lo_Hi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:34.782508+00:00
-- url     : https://prove2.me/submissions/0837418b-cf56-4ec0-a581-7545cf85275b

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_Lo_castSucc
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_Lo_last

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
theorem _root_.solution {n : ℕ} (μ : Fin (n + 1) → ℤ) (l : Fin n → ℤ) :
    ∑ j, Lo μ l j + ∑ i, Hi μ l i = ∑ j, μ j + ∑ i, l i := by
  rw [Fin.sum_univ_castSucc (Lo μ l), Fin.sum_univ_castSucc μ]
  simp only [Lo_castSucc, Lo_last, Hi]
  have h : ∑ i : Fin n, (max (μ i.castSucc) (l i) + min (μ i.castSucc) (l i)) =
      ∑ i : Fin n, (μ i.castSucc + l i) :=
    Finset.sum_congr rfl (fun i _ => by rw [add_comm]; exact min_add_max _ _)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h
  linarith
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
