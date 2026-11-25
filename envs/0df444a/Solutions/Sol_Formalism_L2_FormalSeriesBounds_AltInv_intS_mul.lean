-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.AltInv.intS_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:40:03.577484+00:00
-- url     : https://prove2.me/submissions/a4e7cb7a-b73e-4a6f-9df5-285df090fab4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AltInv
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_sum

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
theorem _root_.solution {f g : MvPowerSeries σ C} (hf : IntS v f) (hg : IntS v g) : IntS v (f * g) := by
  intro μ
  rw [coeff_mul]
  exact intC_sum _ fun p _ => intC_mul (hf _) (hg _)
end Formalism.L2.FormalSeriesBounds.AltInv
