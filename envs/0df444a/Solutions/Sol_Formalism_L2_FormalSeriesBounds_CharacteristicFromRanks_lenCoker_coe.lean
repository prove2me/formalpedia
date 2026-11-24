-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks.lenCoker_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:49.121919+00:00
-- url     : https://prove2.me/submissions/e5a7f479-4b8e-45a3-b6dc-a95288b66ffb

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_vR_apply
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_CharacteristicFromRanks_coe_det

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
theorem _root_.solution (V : VF C) {m h : ℕ} (α : Matrix (Fin m) (Fin h) (intR V)) :
    S4.lenCoker (vR V) α = S4.lenCoker V.v (Matrix.of fun i k => (α i k : C)) := by
  unfold S4.lenCoker
  congr 1
  funext g
  rw [vR_apply, coe_det]
  rfl
end Formalism.L2.FormalSeriesBounds.CharacteristicFromRanks
