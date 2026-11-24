-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.ld_mu_w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:43:15.293614+00:00
-- url     : https://prove2.me/submissions/3775f63f-3dc0-4636-9226-6b484ebcc653

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
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
theorem _root_.solution (p w i q : ℕ) (lam2 : Fin q → ℕ) : mu p w i lam2 (w : ℤ) = 0 := by
  unfold mu
  apply Nat.eq_zero_of_le_zero
  refine Finset.sup_le fun tau htau => ?_
  simp only [shapes, Finset.mem_filter] at htau
  exact htau.2.2.2.2.le
end Formalism.CohomologicalDescent.LD
