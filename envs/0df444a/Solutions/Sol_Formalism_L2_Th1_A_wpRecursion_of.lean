-- Prove2me | solution 1 for Formalism.L2.Th1.A.wpRecursion_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:32:52.494845+00:00
-- url     : https://prove2.me/submissions/ff615d4e-762e-436a-8504-dc763aa3a8a3

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_WpShape
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_cleared_low
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_cleared_odd
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_second_cleared
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_recursion_of
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_wpL_shape

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
open WpSh
namespace Formalism.L2.Th1.A
theorem _root_.solution (hE : ExpSpec.{u}) (hO : WpODE.{u}) : WpRecursion.{u} := by
  intro K _ _ W k hk
  obtain ⟨h1, h2⟩ := wpL_shape hE hO W
  have hs := (hO K W).2.2
  rw [h1] at hs
  have e := recursion_of (second_cleared hs) (cleared_low h2).1 (cleared_odd h2) (k - 1)
    (by omega)
  have k1 : k - 1 - 1 = k - 2 := by omega
  have k2 : 2 * (k - 1) + 2 = 2 * k := by omega
  have k3 : ((k - 1 : ℕ) : K) = (k : K) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [k1, k2, k3] at e
  linear_combination e
end Formalism.L2.Th1.A
