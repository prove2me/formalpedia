-- Prove2me | solution 1 for Formalism.L2.Th1.A.WpSh.add_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:40.177965+00:00
-- url     : https://prove2.me/submissions/e3f10c2e-7cc2-45f9-9442-16009c52dc74

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_WpShape
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_z_mul_zi
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_uPow_neg_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.WpSh
variable {K : Type u} [Field K]
namespace Formalism.L2.Th1.A.WpSh
theorem _root_.solution (r : K⟦X⟧) :
    (uPow (-2) : LaurentSeries K) + toL r = uPow (-2) * toL (1 + X ^ 2 * r) := by
  rw [map_add, map_one, map_mul, map_pow, mul_add, mul_one, uPow_neg_two]
  congr 1
  have h := z_mul_zi (K := K)
  linear_combination (-(toL X * uPow (-1) + 1) * toL r) * h
end Formalism.L2.Th1.A.WpSh
