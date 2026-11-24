-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VF.Ge.mul_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:44.379586+00:00
-- url     : https://prove2.me/submissions/1a212f9c-821d-434b-9a65-78125a00706b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeNatCast
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul

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
theorem _root_.solution {w : ℝ} {a b : C} (ha : V.Ge 0 a) (hb : V.Ge w b) : V.Ge w (a * b) := by
  simpa using Ge.mul ha hb
end Ge
end Formalism.L2.FormalSeriesBounds.VF
