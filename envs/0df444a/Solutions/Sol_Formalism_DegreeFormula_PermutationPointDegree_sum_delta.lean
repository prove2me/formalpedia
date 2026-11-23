-- Prove2me | solution 1 for Formalism.DegreeFormula.PermutationPointDegree.sum_delta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:13:40.668487+00:00
-- url     : https://prove2.me/submissions/539d6cf0-3659-49ee-993f-4d69b8e3383f

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PermExpInj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.DegreeFormula Formalism.DegreeFormula.PermutationPointDegree
open Formalism.DegreeFormula
namespace Formalism.DegreeFormula.PermutationPointDegree
theorem _root_.solution (N : ℕ) : ∑ i : Fin N, (N - 1 - (i : ℕ)) = N * (N - 1) / 2 := by
  rw [← Finset.sum_range_id]
  rw [← Fin.sum_univ_eq_sum_range]
  refine Fintype.sum_equiv Fin.revPerm _ _ ?_
  intro i
  simp [Fin.val_rev]
  omega
end Formalism.DegreeFormula.PermutationPointDegree
