-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.multiplicity_shift_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:22:28.165554+00:00
-- url     : https://prove2.me/submissions/2493faca-9c34-4faf-931e-288850ff6144

import Definitions.Def_Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Theorems.Thm_Formalism_CohomologicalDescent_LD_mem_shapes_iff
import Theorems.Thm_Formalism_CohomologicalDescent_LD_boxes_of_content_shift
import Theorems.Thm_Formalism_CohomologicalDescent_LD_shapes_shift_iff

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
theorem _root_.solution (p w i q c : ℕ) (lam2 : Fin q → ℕ) (x : ℤ) :
    mu p (w + c) i (fun b => lam2 b + c) (x + (c : ℤ)) = mu p w i lam2 x := by
  unfold mu
  apply le_antisymm
  · refine Finset.sup_le fun tau' htau' => ?_
    have hge : ∀ a, c ≤ tau' a := fun a => by
      have := ((mem_shapes_iff _ _ _ _ _ _).mp htau').1 a
      omega
    have he : tau' = fun b => (tau' b - c) + c := funext fun b => by
      have := hge b
      omega
    rw [he] at htau' ⊢
    rw [boxes_of_content_shift]
    exact Finset.le_sup (f := fun tau => boxesOfContent lam2 tau x) ((shapes_shift_iff _ _ _ _ _ _ _).mp htau')
  · refine Finset.sup_le fun tau htau => ?_
    rw [← boxes_of_content_shift q c lam2 tau x]
    exact Finset.le_sup (f := fun tau => boxesOfContent (fun b => lam2 b + c) tau (x + (c : ℤ)))
      ((shapes_shift_iff _ _ _ _ _ _ _).mpr htau)
end Formalism.CohomologicalDescent.LD
