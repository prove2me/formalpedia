-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Phase.eq_one_of_low_up
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:00:11.54798+00:00
-- url     : https://prove2.me/submissions/af8cdc0a-1216-4925-bfe9-f0a9d8414cb9

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_low_zero
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_up_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
open Formalism.DoubleCosetMeasures.P.Phase
variable {K : Type} [CommRing K]
namespace Formalism.DoubleCosetMeasures.P.Phase
theorem _root_.solution {n : ℕ} {m : Matrix (Fin n) (Fin n) K} (h1 : IsLowUni m)
    (h2 : IsUpUni m) : m = 1 := by
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · rw [low_zero h1 h, Matrix.one_apply_ne h.ne]
  · rw [h1.2 i, Matrix.one_apply_eq]
  · rw [up_zero h2 h, Matrix.one_apply_ne h.ne']
end Formalism.DoubleCosetMeasures.P.Phase
