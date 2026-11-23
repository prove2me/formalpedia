-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VF.Ge.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:26:57.524945+00:00
-- url     : https://prove2.me/submissions/598dd1c0-adcc-4efd-8571-01eb53f956f6

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
theorem _root_.solution {w w' : ℝ} {a b : C} (ha : V.Ge w a) (hb : V.Ge w' b) : V.Ge (w + w') (a * b) := by
  show ((w + w' : ℝ) : WithTop ℝ) ≤ V.v (a * b)
  rw [AddValuation.map_mul, WithTop.coe_add]
  exact add_le_add ha hb
end Ge
end Formalism.L2.FormalSeriesBounds.VF
