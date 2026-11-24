-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.linkage_reflection_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:14:39.224275+00:00
-- url     : https://prove2.me/submissions/a406e8f9-75ca-4fdb-bbcf-c049ace4c5c0

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_prod_comp_eq_prod_comp

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
theorem _root_.solution : LinkageFlip := by
  intro K _ N U U' c c' h H
  have H2 := congrArg (fun p => p.comp (-Polynomial.X + Polynomial.C (((-h - c' - c : ℤ)) : K))) H
  simp only [prod_comp_eq_prod_comp, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp] at H2
  have e : ∀ W : Fin N → ℤ, ∀ a : Fin N, -Polynomial.X + Polynomial.C (((-h - c' - c : ℤ)) : K) +
      Polynomial.C (((W a + c : ℤ)) : K) = -(Polynomial.X + Polynomial.C (((h - W a + c' : ℤ)) : K)) := by
    intro W a
    rw [neg_add, add_assoc, ← Polynomial.C_add, ← Polynomial.C_neg]
    congr 2
    push_cast
    ring
  simp only [e, Finset.prod_neg] at H2
  exact ((isUnit_neg_one).pow _).mul_left_cancel H2
end Formalism.CohomologicalDescent.WorkedExample
