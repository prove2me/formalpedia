-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.divided_power_cofactor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:50:11.817742+00:00
-- url     : https://prove2.me/submissions/9f91bb63-3a14-42d1-b730-a7aabe7b8d76

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_eval_neg_x_coeff
import Theorems.Thm_Formalism_CohomologicalDescent_LD_cofactor_intertwines_generator

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
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution {r : ℕ} (a b : Fin r) (hab : a ≠ b) (k : ℕ) (x : MvPolynomial (Fin r × Fin r) ℤ) :
    rowDiv ℤ a b k (cofMap r x) = (-1) ^ k * cofMap r (rowDiv ℤ (Fin.rev b) (Fin.rev a) k x) := by
  unfold rowDiv
  rw [cofactor_intertwines_generator a b hab, eval_neg_x_coeff]
  rfl
end Formalism.CohomologicalDescent.LD
