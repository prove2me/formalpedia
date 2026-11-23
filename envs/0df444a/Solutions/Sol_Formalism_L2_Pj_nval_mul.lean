-- Prove2me | solution 1 for Formalism.L2.Pj.nval_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:43:36.46901+00:00
-- url     : https://prove2.me/submissions/8409ceb1-b49b-43ec-b07d-9797c5c82b1f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Theorems.Thm_Formalism_L2_Pj_vV_mul
import Theorems.Thm_Formalism_L2_Pj_nval_zero
import Theorems.Thm_Formalism_L2_Pj_nval_of_ne
import Theorems.Thm_Formalism_L2_Pj_nval_ne_bot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField
open scoped WithZero
open Formalism Formalism.L2 Formalism.L2.Pj
variable (V : Type) {K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
  [Algebra V K'] [IsFractionRing V K']
variable {V}
variable (V)
variable {V}
namespace Formalism.L2.Pj
theorem _root_.solution (e : ℕ) (x y : K') : nval V e (x * y) = nval V e x + nval V e y := by
  by_cases hx : x = 0
  · subst hx; rw [zero_mul, nval_zero, EReal.top_add_of_ne_bot (nval_ne_bot e y)]
  by_cases hy : y = 0
  · subst hy; rw [mul_zero, nval_zero, EReal.add_top_of_ne_bot (nval_ne_bot e x)]
  rw [nval_of_ne hx, nval_of_ne hy, nval_of_ne (mul_ne_zero hx hy), vV_mul hx hy,
    Int.cast_add, add_div, EReal.coe_add]
end Formalism.L2.Pj
