-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.keyZero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:59.264903+00:00
-- url     : https://prove2.me/submissions/b05ff40c-bee4-4b54-975d-2593223f075a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinrankIntSelf
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_IdempotentLemmas_eS_mul_asAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
open IdempotentLemmas
namespace Formalism.IndefR.LatticeTransfer
theorem _root_.solution : KeyZero := by
  intro K _ G _ _ T _ _ τ V _ _ ρ a ha
  rw [← Module.End.mul_eq_comp]
  simpa [ha] using eS_mul_asAlg τ ρ a
end Formalism.IndefR.LatticeTransfer
