-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.sum_split_three_intervals
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:03:31.38294+00:00
-- url     : https://prove2.me/submissions/900fff78-79b8-43d5-86ce-de11ccadfb2d

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample

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
theorem _root_.solution {N : ℕ} (f : Fin N → ℤ) (x y : ℕ) (hxy : x ≤ y) :
    ∑ a, f a = ∑ a ∈ Finset.univ.filter (fun a : Fin N => (a : ℕ) < x), f a +
      ∑ a ∈ Finset.univ.filter (fun a : Fin N => x ≤ (a : ℕ) ∧ (a : ℕ) < y), f a +
      ∑ a ∈ Finset.univ.filter (fun a : Fin N => y ≤ (a : ℕ)), f a := by
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  split_ifs <;> first | (exfalso; omega) | simp
end Formalism.CohomologicalDescent.WorkedExample
