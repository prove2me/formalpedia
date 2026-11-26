-- Prove2me | solution 1 for BKAR.Forest.deriv_interpWithFill_apply_of_inSameComponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:16:09.089811+00:00
-- url     : https://prove2.me/submissions/b3a15d18-2b46-48de-bb50-772e71673e89

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
import Theorems.Thm_BKAR_Forest_interpWithFill_of_inSameComponent

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V)
    (u : F.EdgeParam → ℝ) {e : Edge V}
    (he : F.inSameComponent e.left e.right) (t : ℝ) :
    deriv (fun s : ℝ => F.interpWithFill u s e) t = 0 := by
  have hfun :
      (fun s : ℝ => F.interpWithFill u s e) =
        fun _ : ℝ => F.pathMin u (F.pathInF e.left e.right he) := by
    funext s
    exact F.interpWithFill_of_inSameComponent u s he
  rw [hfun]
  exact deriv_const t _
end BKAR.Forest
