-- Prove2me | solution 1 for Formalism.L2.Pj.nval_bc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:07.093869+00:00
-- url     : https://prove2.me/submissions/20c5830d-e96b-40be-b35c-29eb7ba42ad4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
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
theorem _root_.solution {V' K'' : Type} [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [Field K'']
    [Algebra V' K''] [IsFractionRing V' K''] (i : K' →+* K'') {r : ℕ} (hr : 0 < r)
    (hi : ∀ x, vV V' (i x) = (r : ℤ) * vV V x) (e : ℕ) (x : K') :
    nval V' (r * e) (i x) = nval V e x := by
  by_cases hx : x = 0
  · subst hx; rw [map_zero, nval_zero, nval_zero]
  rw [nval_of_ne ((map_ne_zero i).2 hx), nval_of_ne hx, hi]
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  congr 1; push_cast; exact mul_div_mul_left _ _ hr'
end Formalism.L2.Pj
