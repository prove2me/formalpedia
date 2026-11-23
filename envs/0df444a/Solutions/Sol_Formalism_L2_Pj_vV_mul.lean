-- Prove2me | solution 1 for Formalism.L2.Pj.vV_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:14.464571+00:00
-- url     : https://prove2.me/submissions/f358d483-28b1-4a8c-bf71-83b2ed52487b

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
theorem _root_.solution {x y : K'} (hx : x ≠ 0) (hy : y ≠ 0) : vV V (x * y) = vV V x + vV V y := by
  simp only [vV, map_mul, WithZero.log_mul (valV_ne_zero hx) (valV_ne_zero hy)]
  ring
end Formalism.L2.Pj
