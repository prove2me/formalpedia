-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.depthDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:25:45.114238+00:00
-- url     : https://prove2.me/submissions/4929cb98-d334-419e-b363-cc811b728b36

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_rev_cast_castAdd_eq_natAdd
import Theorems.Thm_Formalism_CohomologicalDescent_LD_sum_complement_add_sum
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
theorem _root_.solution : DepthDual := by
  intro p q w M i μ hw hμ
  unfold IsDepthLast IsDepth
  simp only [rev_cast_castAdd_eq_natAdd]
  have h0 : ∑ x : Fin p, (M - μ (Fin.natAdd q x.rev)) = ∑ a : Fin p, (M - μ (Fin.natAdd q a)) :=
    Equiv.sum_comp Fin.revPerm fun a : Fin p => M - μ (Fin.natAdd q a)
  rw [h0]
  have h1 := sum_complement_add_sum M (fun a : Fin p => μ (Fin.natAdd q a)) fun a => hμ _
  have h2 : p * w ≤ p * M := Nat.mul_le_mul_left p hw
  rw [Nat.mul_sub]
  generalize p * w = pw at *
  generalize p * M = pM at *
  omega
end Formalism.CohomologicalDescent.LD
