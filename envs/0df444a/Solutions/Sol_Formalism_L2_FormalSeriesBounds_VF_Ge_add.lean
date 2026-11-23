-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VF.Ge.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:26:18.469862+00:00
-- url     : https://prove2.me/submissions/c8710d4d-5ccf-4342-902d-189f6db96c5b

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
theorem _root_.solution {w : ℝ} {a b : C} (ha : V.Ge w a) (hb : V.Ge w b) : V.Ge w (a + b) := le_trans (le_min ha hb) (V.v.map_add a b)
end Ge
end Formalism.L2.FormalSeriesBounds.VF
