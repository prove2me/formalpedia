-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.ld_gen_mem_weyl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:25:48.215868+00:00
-- url     : https://prove2.me/submissions/af012022-e8cc-4c94-8ed9-63385eef80ee

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_hw
import Theorems.Thm_Formalism_CohomologicalDescent_LD_divided_power_one_zero_vector
import Theorems.Thm_Formalism_GradedWeylDivisibility_weylRowDivStable


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
theorem _root_.solution (w y j : ℕ) :
    ((w - y).choose j : ℤ) • vec2 w y j ∈ weyl ℤ 2 2 le_rfl (wt2 w y) := by
  have h0 : hw ℤ le_rfl (wt2 w y) ∈ weyl ℤ 2 2 le_rfl (wt2 w y) :=
    Submodule.subset_span ⟨[], rfl⟩
  have h1 := weylRowDivStable ℤ 2 2 le_rfl (wt2 w y) 1 0 j _ h0
  rw [ld_hw, divided_power_one_zero_vector, zero_add] at h1
  exact h1
end Formalism.CohomologicalDescent.LD
