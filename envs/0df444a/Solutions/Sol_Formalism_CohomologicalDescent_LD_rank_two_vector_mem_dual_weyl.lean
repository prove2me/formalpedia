-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.rank_two_vector_mem_dual_weyl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:25:48.905806+00:00
-- url     : https://prove2.me/submissions/04f513be-21c1-4502-b568-b1087f320fe1

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_anti
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_hw
import Theorems.Thm_Formalism_CohomologicalDescent_LD_divided_power_one_zero_vector
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylSat
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwMem
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivStable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution (w y i : ℕ) (h : y + i ≤ w) : vec2 w y i ∈ dualWeyl ℤ 2 2 (wt2 w y) := by
  have hy : y ≤ w := by omega
  have hhw : vec2 w y 0 ∈ dualWeyl ℤ 2 2 (wt2 w y) := by
    rw [← ld_hw]
    exact hwMem ℤ 2 2 le_rfl (wt2 w y) (ld_anti w y hy)
  have h1 := rowDivStable ℤ 2 2 (wt2 w y) 1 0 i _ hhw
  rw [divided_power_one_zero_vector, zero_add] at h1
  refine dualWeylSat ℤ 2 2 (wt2 w y) _ _ ?_ h1
  have : 0 < (w - y - 0).choose i := Nat.choose_pos (by omega)
  exact_mod_cast this.ne'
end Formalism.CohomologicalDescent.LD
