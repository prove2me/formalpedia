-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.cofactor_map_generic_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:27:00.628993+00:00
-- url     : https://prove2.me/submissions/91551307-01b8-4abd-97f3-f04cfd538a0e

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_CohomologicalDescent_LD_cofactor_of_variable
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
theorem _root_.solution (r : ℕ) : (cofMap r).mapMatrix (genericMatrix' ℤ r) =
    ((genericMatrix' ℤ r).adjugate.transpose).submatrix Fin.revPerm Fin.revPerm := by
  refine Matrix.ext fun a s => ?_
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, Matrix.transpose_apply,
    Fin.revPerm_apply]
  exact cofactor_of_variable r a s
end Formalism.CohomologicalDescent.LD
