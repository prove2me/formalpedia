-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.AltInv.intS_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:33:37.096775+00:00
-- url     : https://prove2.me/submissions/73a20dcc-e396-423a-b401-d5f609cf0405

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AltInv
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_one

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
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.AltInv
variable {C : Type*} [Field C] (v : AddValuation C (WithTop ℝ))
variable {v}
variable {σ τ : Type*}
namespace Formalism.L2.FormalSeriesBounds.AltInv
theorem _root_.solution : IntS v (1 : MvPowerSeries σ C) := by
  intro μ
  rw [coeff_one]
  split_ifs
  · exact intC_one
  · exact intC_zero
end Formalism.L2.FormalSeriesBounds.AltInv
