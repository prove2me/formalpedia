-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VF.Ge.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:26:19.036367+00:00
-- url     : https://prove2.me/submissions/33b4bba7-55b2-4882-8ae2-9df28372b3d1

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
theorem _root_.solution {w w' : ℝ} {a : C} (h : V.Ge w a) (hw : w' ≤ w) : V.Ge w' a := le_trans (WithTop.coe_le_coe.mpr hw) h
end Ge
end Formalism.L2.FormalSeriesBounds.VF
