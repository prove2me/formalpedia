-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VF.Ge.l_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:17:31.017215+00:00
-- url     : https://prove2.me/submissions/5fa724c7-d93b-457c-9d92-664061deff18

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeNatCast
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_l_ne_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_of_l_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Finset
noncomputable section
variable {C : Type*} [Field C]
open Formalism.L2.FormalSeriesBounds.VF
variable (V : VF C)
variable {V}
namespace Formalism.L2.FormalSeriesBounds.VF
namespace Ge
theorem _root_.solution {w : ℝ} {a : C} (h : V.Ge w a) : V.Ge (w - 1) ((V.l : C)⁻¹ * a) := by
  apply Ge.of_l_mul
  rwa [← mul_assoc, mul_inv_cancel₀ l_ne_zero, one_mul]
end Ge
end Formalism.L2.FormalSeriesBounds.VF
