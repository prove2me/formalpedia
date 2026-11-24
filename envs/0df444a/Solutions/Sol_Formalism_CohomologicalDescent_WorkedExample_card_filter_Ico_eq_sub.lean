-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.card_filter_Ico_eq_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:03:24.231006+00:00
-- url     : https://prove2.me/submissions/c9914292-5658-4e2f-a2ca-5b19f69085d1

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
theorem _root_.solution (N x y : ℕ) (hy : y ≤ N) :
    (Finset.univ.filter (fun a : Fin N => x ≤ (a : ℕ) ∧ (a : ℕ) < y)).card = y - x := by
  have e : (Finset.univ.filter (fun a : Fin N => x ≤ (a : ℕ) ∧ (a : ℕ) < y)).map Fin.valEmbedding =
      Finset.Ico x y := by
    ext m
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_Ico]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hm
      exact ⟨⟨m, by omega⟩, hm, rfl⟩
  rw [← Finset.card_map, e, Nat.card_Ico]
end Formalism.CohomologicalDescent.WorkedExample
