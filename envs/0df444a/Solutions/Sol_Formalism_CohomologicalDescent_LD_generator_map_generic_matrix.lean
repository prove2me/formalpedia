-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.generator_map_generic_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:17:16.330066+00:00
-- url     : https://prove2.me/submissions/1719f4f5-8d00-4039-8d78-ba66626d9170

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowGen_X
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
theorem _root_.solution {r : ℕ} (a b : Fin r) : (rowGen ℤ a b).mapMatrix (genericMatrix' ℤ r) =
    Matrix.transvection b a Polynomial.X * Polynomial.C.mapMatrix (genericMatrix' ℤ r) := by
  refine Matrix.ext fun p q => ?_
  by_cases hp : p = b
  · subst hp
    rw [Matrix.transvection_mul_apply_same]
    simp [rowGen_X, genericMatrix']
  · rw [Matrix.transvection_mul_apply_of_ne _ _ _ _ hp]
    simp [rowGen_X, genericMatrix', hp]
end Formalism.CohomologicalDescent.LD
