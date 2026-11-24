-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.prod_X_add_C_shift_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:14:40.771219+00:00
-- url     : https://prove2.me/submissions/efe3d6bb-c3bc-4516-ac57-496a769f87a2

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
theorem _root_.solution {K : Type} [CommRing K] {N : ℕ} (U U' : Fin N → ℤ) (c c' : ℤ)
    (H : (∏ a, (Polynomial.X + Polynomial.C (((U a + c : ℤ)) : K))) =
      ∏ a, (Polynomial.X + Polynomial.C (((U' a + c : ℤ)) : K))) :
    (∏ a, (Polynomial.X + Polynomial.C (((U a + c' : ℤ)) : K))) =
      ∏ a, (Polynomial.X + Polynomial.C (((U' a + c' : ℤ)) : K)) := by
  have H2 := congrArg (fun p => p.comp (Polynomial.X + Polynomial.C (((c' - c : ℤ)) : K))) H
  simp only [prod_comp_eq_prod_comp, Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp] at H2
  have e : ∀ W : Fin N → ℤ, ∀ a : Fin N, Polynomial.X + Polynomial.C (((c' - c : ℤ)) : K) +
      Polynomial.C (((W a + c : ℤ)) : K) = Polynomial.X + Polynomial.C (((W a + c' : ℤ)) : K) := by
    intro W a
    rw [add_assoc, ← Polynomial.C_add]
    congr 2
    push_cast
    ring
  simpa only [e] using H2
end Formalism.CohomologicalDescent.WorkedExample
