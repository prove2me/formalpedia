-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.example_params_satisfy_hyp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:23:50.38346+00:00
-- url     : https://prove2.me/submissions/ebc48ac3-480e-4ba8-89e5-839072958a8d

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_two_pow_sixty_le_example_b
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_example_lstar_eq_b_div
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_example_b_div_lstar_eq

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
theorem _root_.solution : exampleParamsAlt.Hyp := by
  have hb := two_pow_sixty_le_example_b
  have e := example_b_div_lstar_eq
  have e8 : 8 * exampleParamsAlt.b / exampleParamsAlt.lstar = 8 * 1814470 := by rw [mul_div_assoc, e]
  have hl : (2 : ℝ) ^ 60 / 1814470 ≤ exampleParamsAlt.lstar := by rw [example_lstar_eq_b_div]; gcongr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try (simp [exampleParamsAlt]; done)
  · show (6 : ℝ) ≤ exampleParamsAlt.b / _
    simp only [exampleParamsAlt] at *
    rw [le_div_iff₀ (by norm_num)]; norm_num at hb ⊢; linarith
  · rw [e]; simp only [exampleParamsAlt] at *; norm_num at hl ⊢; linarith
  · rw [e8]; simp only [exampleParamsAlt] at *; norm_num at hl ⊢; linarith
end Formalism.CohomologicalDescent.WorkedExample
