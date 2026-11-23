-- Prove2me | solution 1 for Formalism.L2.NX.tvAt_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:13:20.14621+00:00
-- url     : https://prove2.me/submissions/3a670bb5-7530-42fa-8501-07514419a217

import Mathlib
import Definitions.Def_Formalism_AlgebraicWeights_IsAlgWeight
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_ExpDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.NX
variable {ι : Type} [Fintype ι] {p : ι → ℕ} {r : ℕ}
namespace Formalism.L2.NX
theorem _root_.solution [DecidableEq ι] (hr : 2 ≤ r) (x y : ι) :
    ((tvAt (p := p) hr x y : GL (Fin r) (ZMod (p y))) : Matrix (Fin r) (Fin r) (ZMod (p y))) =
      if y = x then tv hr 1 else 1 := by
  unfold tvAt
  by_cases h : y = x
  · subst h
    rw [Pi.mulSingle_eq_same, if_pos rfl]
    rfl
  · rw [Pi.mulSingle_eq_of_ne h, if_neg h]
    simp
end Formalism.L2.NX
