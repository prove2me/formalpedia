-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks.coe_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:01.138105+00:00
-- url     : https://prove2.me/submissions/8a2ecade-8389-4a7b-a9fe-4e938b5f79f5

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks

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
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
open Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
theorem _root_.solution (V : VF C) {m : Type} [Fintype m] [DecidableEq m] (M : Matrix m m (intR V)) :
    ((M.det : intR V) : C) = (Matrix.of fun i k => (M i k : C)).det := by
  rw [show ((M.det : intR V) : C) = (intR V).subtype M.det from rfl, RingHom.map_det]
  rfl
end Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
