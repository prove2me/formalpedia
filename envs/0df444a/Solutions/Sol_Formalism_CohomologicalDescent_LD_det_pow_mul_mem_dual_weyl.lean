-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.det_pow_mul_mem_dual_weyl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:21:59.649345+00:00
-- url     : https://prove2.me/submissions/d7b96114-ea49-4092-abf7-dc29b98b41e2

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LA_det_mul_mem_dual_weyl_shift
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
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution {r : ℕ} (ν : Fin r → ℕ) (c : ℕ) {g : MvPolynomial (Fin r × Fin r) ℤ}
    (hg : g ∈ dualWeyl ℤ r r ν) : genericDet ℤ r ^ c * g ∈ dualWeyl ℤ r r (fun a => ν a + c) := by
  induction c with
  | zero => simpa using hg
  | succ c ih =>
    rw [pow_succ', mul_assoc]
    exact det_mul_mem_dual_weyl_shift (fun a => ν a + c) ih
end Formalism.CohomologicalDescent.LD
