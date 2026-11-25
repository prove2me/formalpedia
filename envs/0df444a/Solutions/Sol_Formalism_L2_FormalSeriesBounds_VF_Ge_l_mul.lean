-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VF.Ge.l_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:17:17.707242+00:00
-- url     : https://prove2.me/submissions/bbcc7b8e-479c-430d-993b-c1a4c9db4e83

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeNatCast

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
theorem _root_.solution {w : ℝ} {a : C} (h : V.Ge w a) : V.Ge (1 + w) ((V.l : C) * a) := by
  show ((1 + w : ℝ) : WithTop ℝ) ≤ V.v ((V.l : C) * a)
  rw [AddValuation.map_mul, V.v_l, WithTop.coe_add, WithTop.coe_one]
  exact add_le_add le_rfl h
end Ge
end Formalism.L2.FormalSeriesBounds.VF
