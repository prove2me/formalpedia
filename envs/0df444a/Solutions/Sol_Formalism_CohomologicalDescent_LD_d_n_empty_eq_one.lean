-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.d_n_empty_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:18:21.26906+00:00
-- url     : https://prove2.me/submissions/9640c05e-fbc9-4d4d-a998-f102b362b74d

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
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
theorem _root_.solution (p w i : ℕ) (f : Fin 0 → ℕ) : Dn p w i f = 1 := by
  unfold Dn
  refine Finset.prod_eq_one fun k _ => ?_
  have h : mu p w i f ((k : ℤ) - ((0 : ℕ) : ℤ)) = 0 := by
    unfold mu
    refine Nat.le_zero.mp (Finset.sup_le fun tau _ => ?_)
    simp [boxesOfContent]
  rw [h, pow_zero]
end Formalism.CohomologicalDescent.LD
