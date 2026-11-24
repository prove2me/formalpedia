-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.strip_data_tensor_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:27:50.614073+00:00
-- url     : https://prove2.me/submissions/7adb0162-9881-44ee-aa26-661aaba24c14

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QxFstInj
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_StripDataTensorColumnFamilies

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution : StripDataTensorColumnFamilies := by
  intro n _ κ _ _ B be Str ps hd M M' e hT ⟨CF⟩
  exact ⟨qx_colFam hd e hT CF⟩
end Formalism.InvariantFactorPaths.ColumnFamilies
