-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.sub_le_sum_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:41:02.916806+00:00
-- url     : https://prove2.me/submissions/8a37a6ea-0cfa-465c-85b7-1353bdb7b5a6

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox

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
theorem _root_.solution {n : ℕ} (ν μ : Fin n → ℤ) (h : ∀ m, μ m ≤ ν m) (i : Fin n) :
    ν i - μ i ≤ ∑ m, ν m - ∑ m, μ m := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.single_le_sum (f := fun m => ν m - μ m) (fun m _ => sub_nonneg.mpr (h m))
    (Finset.mem_univ i)
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri
