-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.peelRows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:59:26.489804+00:00
-- url     : https://prove2.me/submissions/47056834-3cdb-4bd3-8c69-8783b587309c

import Definitions.Def_Formalism_PieriBlockIdeals_BranchingBoundLastGradedOneRow
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Theorems.Thm_Formalism_CohomologicalDescent_LD_exponent_bound_peel_one_row
import Theorems.Thm_Formalism_CohomologicalDescent_LD_expLeMono
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
theorem _root_.solution : PeelRows := by
  intro hD l n s h lam ξ hl ha hh hξ I e hE
  induction s with
  | zero => simpa using hE
  | succ s ih =>
    have ih' := ih (fun a b hab hb => ha a b hab (by omega)) (by
      have := ha (n + s - 1) (n + s) (by omega) (by omega)
      have e1 : n + (s + 1) - 1 = n + s := by omega
      rw [e1] at hh
      omega)
    have h1 := exponent_bound_peel_one_row hD l (n + s) lam ξ hl (fun a b hab hb => ha a b hab (by omega)) hξ I _ ih'
    intro μ hμ
    refine expLeMono l _ _ μ _ _ ?_ (h1 μ hμ)
    have e1 : n + (s + 1) - 1 = n + s := by omega
    rw [e1] at hh
    have h2 : (lam 0 + (n + s) - lam (n + s) - 1) / (l - 1) ≤ (h - 1) / (l - 1) :=
      Nat.div_le_div_right (by omega)
    rw [Nat.succ_mul]
    omega
end Formalism.CohomologicalDescent.LD
