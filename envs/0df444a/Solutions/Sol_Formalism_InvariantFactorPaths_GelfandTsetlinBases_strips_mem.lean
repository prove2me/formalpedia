-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.strips_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:14.405639+00:00
-- url     : https://prove2.me/submissions/f5aaafc4-719a-43ad-b6e2-955fe27639b5

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_mem_stripsUp
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_mem_stripsDown

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
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution : StripsMem := by
  unfold StripsMem
  first
  | exact fun n μ ν b => ⟨Pieri.mem_stripsUp μ ν b, Pieri.mem_stripsDown μ ν b⟩
  | exact ⟨fun n μ ν b => Pieri.mem_stripsUp μ ν b, fun n μ ν b => Pieri.mem_stripsDown μ ν b⟩
  | done
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
