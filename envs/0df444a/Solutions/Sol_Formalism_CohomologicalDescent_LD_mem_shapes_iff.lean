-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.mem_shapes_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:55:39.310609+00:00
-- url     : https://prove2.me/submissions/083cd062-422b-4751-bd4a-adb5acf9280f

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
theorem _root_.solution (p w i q : ℕ) (lam2 tau : Fin q → ℕ) :
    tau ∈ shapes p w i lam2 ↔ (∀ a, lam2 a ≤ tau a ∧ tau a ≤ lam2 a + i) ∧
      (∀ a b : Fin q, a ≤ b → tau b ≤ tau a) ∧ ∑ a, tau a = ∑ a, lam2 a + i ∧
      (∀ b : Fin q, ∀ j < tau b, colLen lam2 tau j ≤ p) ∧ boxesOfContent lam2 tau (w : ℤ) = 0 := by
  simp [shapes, Fintype.mem_piFinset, Finset.mem_Icc]
end Formalism.CohomologicalDescent.LD
