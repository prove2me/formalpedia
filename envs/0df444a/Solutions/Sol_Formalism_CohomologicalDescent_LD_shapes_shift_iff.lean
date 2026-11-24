-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.shapes_shift_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:14:22.721182+00:00
-- url     : https://prove2.me/submissions/aec5e0d2-90f3-4a80-8cea-e3170e0e2755

import Definitions.Def_Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Theorems.Thm_Formalism_CohomologicalDescent_LD_mem_shapes_iff
import Theorems.Thm_Formalism_CohomologicalDescent_LD_boxes_of_content_shift
import Theorems.Thm_Formalism_CohomologicalDescent_LD_column_length_shift
import Theorems.Thm_Formalism_CohomologicalDescent_LD_column_length_below_shift

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
theorem _root_.solution (p w i q c : ℕ) (lam2 tau : Fin q → ℕ) :
    (fun b => tau b + c) ∈ shapes p (w + c) i (fun b => lam2 b + c) ↔ tau ∈ shapes p w i lam2 := by
  rw [mem_shapes_iff, mem_shapes_iff]
  have hbx : boxesOfContent (fun b => lam2 b + c) (fun b => tau b + c) ((w + c : ℕ) : ℤ) =
      boxesOfContent lam2 tau (w : ℤ) := by
    rw [Nat.cast_add]
    exact boxes_of_content_shift q c lam2 tau w
  rw [hbx, Finset.sum_add_distrib, Finset.sum_add_distrib]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨fun a => ?_, fun a b hab => ?_, by omega, fun b j hj => ?_, h5⟩
    · have := h1 a
      omega
    · have := h2 a b hab
      omega
    · rw [← column_length_shift q c]
      exact h4 b (j + c) (by omega)
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨fun a => ?_, fun a b hab => ?_, by omega, fun b j hj => ?_, h5⟩
    · have := h1 a
      omega
    · have := h2 a b hab
      omega
    · by_cases hjc : j < c
      · rw [column_length_below_shift q c lam2 tau j hjc]
        exact Nat.zero_le _
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + c := ⟨j - c, by omega⟩
        rw [column_length_shift]
        exact h4 b j' (by omega)
end Formalism.CohomologicalDescent.LD
