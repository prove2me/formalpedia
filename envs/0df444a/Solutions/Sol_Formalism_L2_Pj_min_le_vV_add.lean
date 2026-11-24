-- Prove2me | solution 1 for Formalism.L2.Pj.min_le_vV_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:16:47.281308+00:00
-- url     : https://prove2.me/submissions/c8d386b4-2177-4685-820c-ec0cd5e2bb2f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Theorems.Thm_Formalism_L2_Pj_valV_ne_zero

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
namespace Formalism.L2.Pj
theorem _root_.solution {x y : K'} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (vV V x) (vV V y) ≤ vV V (x + y) := by
  have h := (valV V).map_add x y
  rcases max_choice (valV V x) (valV V y) with hm | hm <;> rw [hm] at h
  · have := (WithZero.log_le_log (valV_ne_zero hxy) (valV_ne_zero hx)).2 h
    exact (min_le_left _ _).trans (by simp only [vV]; omega)
  · have := (WithZero.log_le_log (valV_ne_zero hxy) (valV_ne_zero hy)).2 h
    exact (min_le_right _ _).trans (by simp only [vV]; omega)
end Formalism.L2.Pj
