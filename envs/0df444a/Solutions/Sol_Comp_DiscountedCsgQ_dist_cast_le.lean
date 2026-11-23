-- Prove2me | solution 1 for Comp.DiscountedCsgQ.dist_cast_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:01:55.557928+00:00
-- url     : https://prove2.me/submissions/6b1fa83b-e415-42dc-98d2-84f1191ed069

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_DiscountedValueIteration
import Definitions.Def_Comp_Iterate

set_option autoImplicit true
open Comp
open Csg
open Comp.DiscountedCsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
namespace Comp.DiscountedCsgQ
theorem _root_.solution {v w : S → ℚ} {d : ℚ} (hd0 : 0 ≤ d) (hd : ∀ s, |v s - w s| ≤ d) :
    dist (fun s => ((v s : ℚ) : ℝ)) (fun s => ((w s : ℚ) : ℝ)) ≤ ((d : ℚ) : ℝ) := by
  refine (dist_pi_le_iff (by exact_mod_cast hd0)).mpr fun s => ?_
  rw [Real.dist_eq]
  have h1 : ((|v s - w s| : ℚ) : ℝ) ≤ ((d : ℚ) : ℝ) := by exact_mod_cast hd s
  push_cast at h1
  exact h1
end Comp.DiscountedCsgQ
