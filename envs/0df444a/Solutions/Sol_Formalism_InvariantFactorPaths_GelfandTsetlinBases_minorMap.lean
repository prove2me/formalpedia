-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.minorMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:41:58.132545+00:00
-- url     : https://prove2.me/submissions/8438e803-1cd5-4a23-9593-9de9e4bfaeae

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
theorem _root_.solution : MinorMap := by
  intro R R' _ _ φ n m I J
  unfold minorF
  split_ifs with h
  · rw [RingHom.map_det]
    rfl
  · exact map_zero φ
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
