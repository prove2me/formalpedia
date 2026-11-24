-- Prove2me | solution 1 for Formalism.MainNotions.DIV.HookProducts.RBTie.emb_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:59:20.655315+00:00
-- url     : https://prove2.me/submissions/7dd2cb39-c151-43bf-823d-9ef902c56f17

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieFrame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField Module
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.DIV Formalism.MainNotions.DIV.HookProducts Formalism.MainNotions.DIV.HookProducts.RBTie
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}
namespace Formalism.MainNotions.DIV.HookProducts.RBTie
theorem _root_.solution (v : InfinitePlace K) (k : Fin d) :
    (fun l => v.embedding ((Pi.single k (1 : K) : Fin d → K) l)) = Pi.single k (1 : ℂ) := by
  funext l
  by_cases h : l = k
  · subst h; simp
  · simp [Pi.single_apply, h]
end Formalism.MainNotions.DIV.HookProducts.RBTie
