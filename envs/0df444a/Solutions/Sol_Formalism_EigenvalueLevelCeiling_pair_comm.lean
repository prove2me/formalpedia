-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.pair_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:40.194798+00:00
-- url     : https://prove2.me/submissions/e2134703-68e1-4eef-a685-c54efbee14d2

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_Mirabolic
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_pairU_apply
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_pairV_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.EigenvalueLevelCeiling
variable {k : Type} [Field k] {n : ℕ}
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (s l : Fin n) (t : k) :
    pairU h s l t * h = h * pairV h s l t := by
  ext a b
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [pairU_apply, pairV_apply, add_mul, mul_add, Finset.sum_add_distrib]
  have e1 : ∑ c, (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a c * h c b = h a b := by
    simp [Matrix.one_apply]
  have e2 : ∑ c, h a c * (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) c b = h a b := by
    simp [Matrix.one_apply]
  rw [e1, e2]
  simp [mul_ite, ite_mul]
  ring
end Formalism.EigenvalueLevelCeiling
