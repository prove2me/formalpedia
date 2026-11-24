-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.boxes_of_content_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:55:34.080996+00:00
-- url     : https://prove2.me/submissions/7411c655-da8c-4b00-a251-15932dce14e3

import Definitions.Def_Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution (q c : ℕ) (lam2 tau : Fin q → ℕ) (x : ℤ) :
    boxesOfContent (fun b => lam2 b + c) (fun b => tau b + c) (x + (c : ℤ)) = boxesOfContent lam2 tau x := by
  unfold boxesOfContent
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  push_cast
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> omega
end Formalism.CohomologicalDescent.LD
