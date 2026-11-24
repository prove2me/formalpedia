-- Prove2me | solution 1 for Formalism.IndefR.Eqv.iterSymmR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:43:16.648233+00:00
-- url     : https://prove2.me/submissions/37bbd3d9-bc18-4d0d-b78f-a675fe07c467

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_IterSymmR
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_SobSym
import Theorems.Thm_Formalism_IndefR_Eqv_iterSymm_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IndefR Formalism.IndefR.Eqv
open scoped ContDiff
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.IndefR.Eqv
theorem _root_.solution : IterSymmR := by
  intro E H _ _ _ _ g hg n
  match n with
  | 0 =>
    intro x v σ
    have : σ = 1 := Equiv.ext fun a => a.elim0
    rw [this]; rfl
  | m + 1 =>
    induction m generalizing H g with
    | zero =>
      intro x v σ
      have : σ = 1 := Equiv.ext fun a => Fin.ext (by have := (σ a).isLt; have := a.isLt; simp)
      rw [this]; rfl
    | succ m ih => exact iterSymm_succ m (fun H _ _ g hg => ih H g hg) H g hg
end Formalism.IndefR.Eqv
