-- Prove2me | solution 1 for Formalism.L2.Pj.nval_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:24:02.221127+00:00
-- url     : https://prove2.me/submissions/4c7ff3ae-5483-4531-bc9b-06715100e829

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Theorems.Thm_Formalism_L2_Pj_min_le_vV_add
import Theorems.Thm_Formalism_L2_Pj_nval_zero
import Theorems.Thm_Formalism_L2_Pj_nval_of_ne

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
theorem _root_.solution (e : ℕ) (x y : K') : min (nval V e x) (nval V e y) ≤ nval V e (x + y) := by
  by_cases hxy : x + y = 0
  · rw [hxy, nval_zero]; exact le_top
  by_cases hx : x = 0
  · subst hx; simp
  by_cases hy : y = 0
  · subst hy; simp
  rw [nval_of_ne hx, nval_of_ne hy, nval_of_ne hxy]
  rcases min_le_iff.1 (min_le_vV_add (V := V) hx hy hxy) with h | h
  · exact min_le_iff.2 (Or.inl (EReal.coe_le_coe_iff.2
      (div_le_div_of_nonneg_right (by exact_mod_cast h) (Nat.cast_nonneg e))))
  · exact min_le_iff.2 (Or.inr (EReal.coe_le_coe_iff.2
      (div_le_div_of_nonneg_right (by exact_mod_cast h) (Nat.cast_nonneg e))))
end Formalism.L2.Pj
