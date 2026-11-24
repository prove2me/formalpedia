-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.gelfand_tsetlin_pieri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:38:57.616075+00:00
-- url     : https://prove2.me/submissions/87cac8b3-775e-4151-8659-c69d2493669d

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_up
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_down

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
theorem _root_.solution : GTPieri := by
  unfold GTPieri
  first
  | exact fun n μ b hμ => ⟨Pieri.up n μ b hμ, Pieri.down n μ b hμ⟩
  | exact ⟨fun n μ b hμ => Pieri.up n μ b hμ, fun n μ b hμ => Pieri.down n μ b hμ⟩
  | done
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
