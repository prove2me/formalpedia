-- Prove2me | solution 1 for Formalism.L2.Pj.nval_mul_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:25.89081+00:00
-- url     : https://prove2.me/submissions/5a21916f-a262-4d5c-a84f-ca259d33db89

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Theorems.Thm_Formalism_L2_Pj_nval_of_ne
import Theorems.Thm_Formalism_L2_Pj_nval_mul

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
theorem _root_.solution (e : ℕ) {u : K'} (hu : u ≠ 0) (hu0 : vV V u = 0) (x : K') :
    nval V e (u * x) = nval V e x := by
  rw [nval_mul, nval_of_ne hu, hu0]; simp
end Formalism.L2.Pj
