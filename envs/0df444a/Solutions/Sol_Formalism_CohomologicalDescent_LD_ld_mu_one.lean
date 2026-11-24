-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.ld_mu_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:55:28.349365+00:00
-- url     : https://prove2.me/submissions/df7ce0fd-c42a-40dc-bd63-aa633b4bd25e

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_shapes_one
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
theorem _root_.solution (p w y i : ℕ) (hp : 1 ≤ p) (h : y + i ≤ w) (c : ℤ) :
    mu p w i (fun _ : Fin 1 => y) c = if (y : ℤ) ≤ c ∧ c < (y : ℤ) + (i : ℤ) then 1 else 0 := by
  rw [mu, ld_shapes_one p w y i hp h, Finset.sup_singleton]
  unfold boxesOfContent
  rw [Finset.univ_unique, Finset.filter_singleton]
  have h0 : ((default : Fin 1).val : ℤ) = 0 := by simp
  simp only [h0, add_zero]
  push_cast
  split_ifs <;> simp
end Formalism.CohomologicalDescent.LD
