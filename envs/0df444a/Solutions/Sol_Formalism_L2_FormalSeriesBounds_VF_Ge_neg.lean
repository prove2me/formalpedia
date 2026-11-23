-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VF.Ge.neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:06.303513+00:00
-- url     : https://prove2.me/submissions/3db4ea3c-7e2e-471b-a63f-75bc4fd61c42

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
theorem _root_.solution {w : ℝ} {a : C} (ha : V.Ge w a) : V.Ge w (-a) := by
  show ((w : ℝ) : WithTop ℝ) ≤ V.v (-a)
  rw [AddValuation.map_neg]
  exact ha
end Ge
end Formalism.L2.FormalSeriesBounds.VF
