-- Prove2me | solution 1 for Formalism.DegreeFormula.PPowSum.degFlHomog
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:40.284489+00:00
-- url     : https://prove2.me/submissions/9bab9c9c-bf79-42f3-bdaf-391a12da8eaa

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PermExpInj
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PowSum
import Theorems.Thm_Formalism_DegreeFormula_PPowSum_degree_permExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.DegreeFormula Formalism.DegreeFormula.PPowSum
open Formalism.DegreeFormula
namespace Formalism.DegreeFormula.PPowSum
theorem _root_.solution : DegFlHomog := by
  intro ι _ _ N d P hP hd
  unfold degFl
  rw [Finset.sum_eq_zero, mul_zero]
  intro σ _
  rw [hP.coeff_eq_zero, mul_zero]
  rw [degree_permExp]
  exact Ne.symm hd
end Formalism.DegreeFormula.PPowSum
