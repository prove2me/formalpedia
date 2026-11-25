-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.term_c_small_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:24:36.204504+00:00
-- url     : https://prove2.me/submissions/830c3603-e99c-480a-81d8-ab8cdc542843

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_tail_line_c_holds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_ex_mul_log_le_of_thickA
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_two_le_prime_cast


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.WorkedExample
open Formalism.CohomologicalDescent
namespace Formalism.CohomologicalDescent.WorkedExample
theorem _root_.solution : TermCSmall := by
  intro P H G hf ι D hA τ hτ l hl hlt
  have hL : 0 ≤ P.L := by have := G.L_ge; linarith
  have lp : (0 : ℝ) < l := by have := LogSmallConstantBounds.two_le_prime_cast hl; linarith
  have a1 := LogSmallConstantBounds.ex_mul_log_le_of_thickA H G hA hτ hl
  have te := H.t_le
  obtain ⟨c1, c2, c3⟩ := (tail_line_c_holds P H hf hL).2.2 (l : ℝ) lp.le (by linarith)
  rw [le_div_iff₀ lp]
  calc (D.ex τ l : ℝ) * Real.log (l : ℝ) * (l : ℝ) ≤ ((P.Nr : ℝ) ^ 2 * P.L) * (l : ℝ) := by gcongr
    _ = (l : ℝ) * (P.Nr : ℝ) ^ 2 * P.L := by ring
    _ ≤ _ := le_trans c1 (le_trans c2 c3)
end Formalism.CohomologicalDescent.WorkedExample
