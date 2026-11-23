-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VF.Ge.sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:27:17.009929+00:00
-- url     : https://prove2.me/submissions/e4bf1a6c-aa13-4751-971b-af12aa604982

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GeNatCast
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add

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
theorem _root_.solution {ι : Type*} {s : Finset ι} {f : ι → C} {w : ℝ} (h : ∀ i ∈ s, V.Ge w (f i)) :
    V.Ge w (∑ i ∈ s, f i) := Finset.sum_induction f (fun x => V.Ge w x) (fun _ _ ha hb => Ge.add ha hb) (Ge.zero w) h
end Ge
end Formalism.L2.FormalSeriesBounds.VF
