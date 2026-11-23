-- Prove2me | solution 1 for Formalism.LogVandermondeBounds.product_first_zeroth_parts.sum_eps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:38.465798+00:00
-- url     : https://prove2.me/submissions/33584112-583c-48ae-8447-f07c91729377

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_MulSingleMulApplySelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.product_first_zeroth_parts
open Finset
variable {ι H K : Type} [Fintype ι] [DecidableEq ι] [Group H] [Fintype H] [DecidableEq H] [Field K]
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts
theorem _root_.solution (a t : H) (ha : a ≠ 1) : ∑ c : H, (eps a (c * t) : K) = 0 := by
  have key : ∀ h : H, (eps a h : K) = (if h = a then 1 else 0) + (if h = 1 then -1 else 0) := by
    intro h
    unfold eps
    by_cases h1 : h = a
    · subst h1
      simp [ha]
    · simp [h1]
  rw [show (∑ c : H, (eps a (c * t) : K)) = ∑ h : H, (eps a h : K) from
    Equiv.sum_comp (Equiv.mulRight t) (fun h => (eps a h : K))]
  simp only [key, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring
end Formalism.LogVandermondeBounds.product_first_zeroth_parts
