-- Prove2me | solution 1 for Formalism.IndefR.U2.mem_eigPart
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:41:13.592972+00:00
-- url     : https://prove2.me/submissions/0acb51fe-664c-45e2-824b-230702b5fc30

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_NormalDecomposition_DecompOfNormalStatement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.U2
variable {I : Type*} {A B : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℂ A] [NormedAddCommGroup B] [InnerProductSpace ℂ B]
namespace Formalism.IndefR.U2
theorem _root_.solution {op : I → Module.End ℂ A} {c : I → ℂ} {x : A} :
    x ∈ eigPart op c ↔ ∀ i, op i x = c i • x := by
  simp only [eigPart, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero]
end Formalism.IndefR.U2
