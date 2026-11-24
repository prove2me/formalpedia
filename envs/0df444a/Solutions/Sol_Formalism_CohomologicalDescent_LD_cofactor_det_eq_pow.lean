-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.cofactor_det_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:34:46.509138+00:00
-- url     : https://prove2.me/submissions/1871d38e-1b15-443c-aff4-ece903c7e86c

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_cofactor_map_generic_matrix

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
theorem _root_.solution (r : ℕ) : cofMap r (genericDet ℤ r) = genericDet ℤ r ^ (r - 1) := by
  unfold genericDet
  rw [AlgHom.map_det, cofactor_map_generic_matrix, Matrix.det_submatrix_equiv_self, Matrix.det_transpose, Matrix.det_adjugate,
    Fintype.card_fin]
end Formalism.CohomologicalDescent.LD
