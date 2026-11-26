-- Prove2me | solution 1 for BKAR.Forest.deriv_interpWithFill_apply_of_not_inSameComponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:24:33.249585+00:00
-- url     : https://prove2.me/submissions/c3d16483-ccbb-4552-93cb-26dc94624bca

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
import Theorems.Thm_BKAR_Forest_interpWithFill_of_not_inSameComponent


set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V)
    (u : F.EdgeParam → ℝ) {e : Edge V}
    (he : ¬ F.inSameComponent e.left e.right) (t : ℝ) :
    deriv (fun s : ℝ => F.interpWithFill u s e) t = 1 := by
  have hfun :
      (fun s : ℝ => F.interpWithFill u s e) = fun s : ℝ => s := by
    funext s
    exact F.interpWithFill_of_not_inSameComponent u s he
  rw [hfun]
  change deriv (id : ℝ → ℝ) t = 1
  exact deriv_id (𝕜 := ℝ) (x := t)
end BKAR.Forest
