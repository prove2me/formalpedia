-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.example_order_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:18:56.683795+00:00
-- url     : https://prove2.me/submissions/f1220c7d-11d5-4956-b25d-38e25a837582

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_append_strictAnti

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
theorem _root_.solution : ParameterStrictOrder := by
  intro p q' t v β e hv hβ h1 h2 h3
  unfold exampleParameterVector
  refine append_strictAnti _ _ ?_ (fun a b hab => neg_lt_neg (hβ hab)) ?_
  · refine append_strictAnti _ _ hv ?_ ?_
    · intro a b hab
      have h' : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := Nat.cast_lt.mpr hab
      try dsimp only
      linarith
    · intro i a
      have h0 : (0 : ℝ) ≤ ((a : ℕ) : ℝ) := Nat.cast_nonneg _
      have := h1 i
      try dsimp only
      linarith
  · intro i c
    induction i using Fin.addCases with
    | left i =>
      simp only [Fin.append_left]
      exact h3 i c
    | right a =>
      simp only [Fin.append_right]
      have ha : ((a : ℕ) : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast Nat.succ_le_of_lt a.isLt
      have := h2 c
      linarith
end Formalism.CohomologicalDescent.WorkedExample
