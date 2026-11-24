-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VF.ge_l
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:18.005432+00:00
-- url     : https://prove2.me/submissions/426d4ef5-02cb-4198-8276-87902c5c909a

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
theorem _root_.solution : V.Ge 1 (V.l : C) := (le_of_eq WithTop.coe_one).trans V.v_l.symm.le
end Formalism.L2.FormalSeriesBounds.VF
