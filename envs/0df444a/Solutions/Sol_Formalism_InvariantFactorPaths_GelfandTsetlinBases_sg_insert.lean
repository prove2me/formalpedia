-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.sg_insert
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:50.625073+00:00
-- url     : https://prove2.me/submissions/9a9a4896-a3a3-4ca6-b995-c3ea0d571955

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract

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
variable {R : Type*} [CommRing R] {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution {I : Finset (Fin n)} {m : Fin n} (hm : m ∉ I) (m' : Fin n) :
    sg (insert m I) m' = sg I m' * (if m' < m then -1 else 1) := by
  unfold sg
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (fun hmem => hm (Finset.mem_filter.mp hmem).1), pow_succ]
  · rw [mul_one]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
